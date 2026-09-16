# PLAN-COMPLETITUD-FINITISTA.md — dos objetivos, un bloqueante común

**Última actualización:** 2026-09-14 · **Autor:** Julián Calderón Almendros

> 🏁🏁 **PASOS 0 y 1 EJECUTADOS el 2026‑09‑14** (ADR‑033, ADR‑034). `Derives₀` está en el build
> (`Derives₀.rec` mide `[propext]`) **y su SOLIDEZ está demostrada**:
> `derives0_soundness : Γ ⊢₀ f → Γ ⊨ f`, footprint `[propext, Classical.choice, Quot.sound]` —
> **cero axiomas del proyecto**.
> ⭐⭐ Con ella salen **`derives0_consistent`** (la primera consistencia de un cálculo de FOL⁼ en
> el proyecto) y **`derives0_not_complete`** (`Derives₀` **no** decide toda fórmula ⇒ el Paso 0
> sirvió para lo que tenía que servir). ⭐ Y RPP **no se movió**: sigue en 145 jobs.

> # 🏁🏁🏁 **VÍA W CERRADA — 2026‑09‑16** (ADR‑039, ADR‑040, ADR‑041)
>
> ```
> completeness₀         : Γ ⊨ f → Γ ⊢₀ f
> derives0_complete_iff : (Γ ⊢₀ f) ↔ (Γ ⊨ f)
> ```
>
> `FOL/Canonical0.lean`, footprint `[propext, Classical.choice, Quot.sound]`, **cero axiomas del
> proyecto**. ⭐⭐ **Las dos direcciones sobre un mismo cálculo de FOL⁼**, por primera vez en el
> proyecto.
>
> ⛔ **Y el entregable es el que este plan anunciaba: un `Classical.choice` EXPLICADO.** Está
> localizado en **una línea** —el `if IsConsistent₀ (Sₙ ∪ {φₙ})` de `FOL.Lindenbaum0`, Π⁰₁— y es
> exactamente el WKL. Ver §6.3.
>
> ⬜ **Queda la vía H** (Herbrand / disyunción finita), §5 — que es el contenido **finitario**.
>
> ## Los dos objetivos, decididos
>
> | | objetivo | ¿finitista? | qué se puede publicar |
> |---|---|---|---|
> | **H** | **Herbrand / disyunción finita** | ✅ **sí, de verdad** | un certificado **finito** y verificable; net‑0 puro, sin modelos ni elección |
> | **W** | **Completitud para `Γ` numerable/r.e.** | ⚠️ no directa, **sí reducible** | ≡ **WKL₀** sobre RCA₀, y WKL₀ es **Π⁰₂‑conservativo sobre PRA** |
>
> ⛔ **Y las dos comparten un bloqueante que va PRIMERO**: hoy no hay ningún cálculo de FOL⁼ sobre
> el que estos teoremas signifiquen lo que dicen. Ver §3.
>
> ⚠️ **Este documento es un PLAN.** Lleva mediciones y estimaciones, y **están etiquetadas**. Una
> estimación sin etiqueta es una medición falsa (ADR‑032 §4).

---

## 0 · Qué se persigue, y qué NO

**NO** se persigue «demostrar la completitud de Gödel de forma finitista». Eso es imposible en
sentido estricto y conviene decirlo antes de empezar: el teorema afirma que existe un **modelo**
—un objeto infinito— y su existencia es una rama de un árbol Π⁰₁.

Se persiguen **dos enunciados distintos**, con precios distintos, que entre los dos dicen dónde
está exactamente el contenido no finitario:

* **H** — el **certificado finito**: de una prueba de `∃x̄ φ(x̄)` con `φ` sin cuantificadores,
  extraer términos `t̄₁…t̄ₙ` tales que `φ(t̄₁) ∨ … ∨ φ(t̄ₙ)` sea tautología. Sintáctico de punta a
  punta. **Es lo que Hilbert quería.**
* **W** — la **completitud model‑teórica**, restringida a `Γ` numerable/r.e., **con su reducción
  declarada**: no se elimina `Classical.choice`, se **documenta** que es exactamente el WKL y que
  WKL₀ no añade teoremas Π⁰₂ sobre PRA.

🔑 **El valor de hacer las dos**: H da el contenido finitario; W dice qué se añade al pasar al
modelo. Por separado, cada una miente por omisión.

---

## 1 · Lo que la metamatemática ya decidió (literatura, no medición de este repo)

* Completitud para lenguajes numerables ≡ **WKL₀** sobre RCA₀ — Simpson, *SOSOA*, Teorema IV.3.3.
* **WKL₀ es Π⁰₂‑conservativo sobre PRA** (Friedman; *SOSOA* IX.3) ⇒ **finitistamente reducible**
  en el sentido de Hilbert/Tait.
* **No es constructiva**: WKL falla en realizabilidad recursiva — hay un árbol binario computable
  e infinito sin rama computable (Kleene).
* **Herbrand** y la **eliminación de cortes** son finitarios: demostrables en PRA.

⇒ La frase exacta que este plan puede acabar publicando es: *«la completitud de FOL⁼ para teorías
numerables es finitistamente REDUCIBLE, y su contenido finitario es Herbrand»*. Ni más ni menos.

---

## 2 · El estado medido de partida (2026‑09‑14)

✅ **Lo que ya está pagado** — todo net‑0 puro, medido:

| pieza | dónde | footprint |
|---|---|---|
| enumerabilidad de `Formula`, **computable** | `../FOL/FOL/Enumeration.lean` (ADR‑030) | `[propext, Classical.choice, Quot.sound]` |
| congruencias de la igualdad | `../FOL/FOL/Theorems/Eq.lean` (ADR‑031) | **`[propext, Quot.sound]`** desde el arreglo del 09‑14 |
| Lema de Lindenbaum | `cuarentena/Completeness.lean` | `[propext, Classical.choice, Quot.sound]`, **incondicional** |
| modelo canónico y **Lema de la Verdad** | ídem | net‑0 puros |
| solidez de un cálculo sin axiomas habitándolo | `sondeos/AnclaSoundness.lean` (`prf0_soundness`) | net‑0 puro |

⛔ **Lo que NO está**, y es de fondo:

1. **`Derives` es sintácticamente COMPLETO** (`derives_complete`, tres líneas, medido) porque
   `raa` toma una **función de Lean**. ⇒ decide toda fórmula ⇒ **no es r.e.** y **no es sólido**.
2. **`FOL.soundness` es FALSO** y con `raa` da `False` sin hipótesis
   (`../FOL/cuarentena/Inconsistencia.lean`).
3. ⇒ **Ningún teorema metateórico sobre `Derives` significa lo que su nombre dice.** Es ADR‑024
   (M‑10) otra vez: `⊢` es la **herramienta**, no el **sujeto**.
4. `henkin_extension_lemma` **sale**, pero pagándolo entra `raa` en el footprint ⇒ **se queda por
   decisión** (ADR‑032, opción A).

---

## 3 · 🏁 PASO 0 — **HECHO** (2026‑09‑14) · `Derives₀`, el cálculo del que sí se puede hablar

### 3.1 · Qué es

Un `inductive Derives₀` **nuevo**, en FOL, con los constructores de `Derives` **menos `gen_rule`**,
y **sin** los cuatro axiomas de `MetaRules`. Más el encaje

    derives0_to_derives : Derives₀ Γ f → Derives Γ f

que es recursión estructural trivial (legal: `Derives₀` no tiene habitantes‑axioma).

### 3.2 · Por qué se puede — ⭐ MEDIDO hoy

El `inductive` **pelado** ya tiene versiones OBJETO de las cuatro meta‑reglas. Compilado con
`import FOL.FOL` **sin** `MetaRules`, las seis salen con footprint **`[propext]`**:

| meta‑regla (axioma) | equivalente objeto (constructor) |
|---|---|
| `imp_intro (Γ ⊢ A → Γ ⊢ B)` | `Derives.intro_impl : Derives (A :: Γ) B → …` |
| `raa (Γ ⊢ A → Γ ⊢ ⊥)` | `Derives.intro_impl` con `B := ⊥` |
| `or_elim` | `Derives.elim_or` |
| `ex_elim` | `Derives.elim_ex` |
| *(y además)* `dne` | `Derives.dne_rule` / `Derives.dne_schema` |

⇒ **Lo que los cuatro axiomas añaden es sólo la fuerza META**, que es exactamente la patología.
`Derives` tiene **22 constructores** (medido); `Derives₀` tendría **21**.

### 3.3 · ⚠️ Por qué se quita también `gen_rule`

`gen_rule : (∀ n : Term, Derives Γ A[n]) → Derives Γ (∀A)` tiene **premisa infinitaria**: es la
ω‑regla sobre términos. Un cálculo **finitario** no la lleva. La introducción de `∀` la da
`Derives.intro_forall` (regla de la eigenvariable, con De Bruijn), que es finitaria y estándar.

⭐ **Y el coste es cero para lo que ya hay**: `cuarentena/Completeness.lean` usa **14
constructores distintos de `Derives` y `gen_rule` NO está entre ellos** (medido). El desarrollo de
completitud entero vive ya dentro del fragmento finitario.

### 3.4 · ⭐ Por qué esto NO toca ROBINSON_PlusPlus

`Derives₀` es un **objeto nuevo para la metateoría**, no un reemplazo. RPP sigue usando `Derives`
y sus meta‑reglas exactamente igual: `gen` **323 usos**, los cuatro axiomas **320**, los
constructores `Derives.*` **164** (censo del 2026‑09‑12). **Ni una cita cambia.**

⇒ **Esto es mucho más barato que la «reparación de fondo»** que propone
`../FOL/cuarentena/README.md` §8 (partir `Derives`/`DerivesW`), y da lo mismo para el objetivo:
un cálculo sobre el que M‑11 no aplica.

### 3.5 · 🏁 Lo que se ejecutó, y lo que costó de verdad

`../FOL/FOL/Derives0.lean`, dentro del barrel `FOL` (`@[default_target]`). **Compiló a la
primera.**

| medida | valor |
|---|---|
| `Derives₀.rec` | **`[propext]`** — cero axiomas del proyecto ⇒ criterio §9 cumplido |
| `derives0_to_derives` | `[propext]` |
| constructores | **21** (los 22 de `Derives` menos `gen_rule`) |
| build FOL | 22 → **23 jobs** |
| ⭐ build RPP | **145 jobs, sin cambio** — ni una cita tocada |
| coste real | ~190 líneas con documentación; ~120 de código |

⭐ **La prueba de que el paso funciona es el propio encaje**: `derives0_to_derives` se demuestra
**por inducción sobre `Derives₀`**, que sobre `Derives` sería ilegítima (M‑11). Veintiún casos,
cada uno su constructor homónimo.

⚠️ La recíproca **no vale, y a propósito**: `Derives` tiene los cuatro habitantes‑axioma y la
ω‑regla. La metateoría vive de este lado; `Derives` se queda como herramienta (ADR‑024).

⭐ De paso, el catálogo de `../FOL/REFERENCE.md` listaba como **vivos** `Soundness.lean`,
`Compacity.lean` y `Completeness.lean`, que están en `cuarentena/` desde hace dos días, y **no
listaba** `Enumeration.lean`. Corregido.

---

## 4 · 🏁 PASO 1 — **HECHO** (2026‑09‑14) · La solidez, **antes** que la completitud

    derives0_soundness : Derives₀ Γ f → Γ ⊨ f

Inducción sobre los 21 constructores. **M‑11 ya no bloquea** (cero habitantes‑axioma), y la
plantilla está escrita: `prf0_soundness` hizo exactamente esto para `Prf₀`, net‑0 puro, con
`FOL/Semantics.lean`, que ya existe y ya es correcto.

⚠️⚠️ **Éste es el agujero de verdad del repo, y va antes que todo lo demás.** Hoy hay un cálculo
cuya solidez es **falsa**; eso pesa más que no tener la completitud. Y sin solidez, una completitud
no dice nada: `⊢₀ f ↔ Γ ⊨ f` sólo tiene contenido con las **dos** direcciones.

### 4.1 · 🏁 Lo que se ejecutó

`../FOL/FOL/Soundness0.lean`, en el build.

| medida | valor |
|---|---|
| `derives0_soundness` | `[propext, Classical.choice, Quot.sound]` — **cero axiomas del proyecto** ⇒ criterio §9 cumplido |
| 🏁 `derives0_consistent : ¬ ([] ⊢₀ ⊥)` | ídem — **la primera consistencia de un cálculo de FOL⁼ en el proyecto** |
| 🏁🏁 `derives0_not_complete` | ídem — hay `A` con `[] ⊬₀ A` y `[] ⊬₀ ¬A` |
| build FOL | 23 → **24 jobs** · RPP **145, sin cambio** |

⭐⭐ **`derives0_not_complete` es el que certifica el Paso 0.** `Derives` **sí** es sintácticamente
completo —`raa` toma una función de Lean ⇒ lo que no prueba, lo refuta—, y ésa es la patología que
lo inhabilita como sujeto (ADR‑024, M‑10: completo ⇒ **no r.e.**). `Derives₀` **no lo es**, y la
prueba son dos modelos sobre `Unit`: uno con todas las relaciones verdaderas y otro con todas
falsas.

⇒ 🔑 **`Derives₀` es sólido, consistente y no decide todo.** Es un cálculo del que se puede decir
algo — que es exactamente lo que este plan necesitaba de §3 y §4.

⭐ **Y costó mucho menos de lo estimado**, por una razón que conviene guardar: los **18 casos
originales se rescataron de `../FOL/cuarentena/Soundness.lean`**. Aquella prueba **era correcta
caso por caso** —deducción natural intuicionista, cada regla semánticamente válida—; lo que la
invalidaba era **el tipo sobre el que inducía**. 🔑 *Cuando un teorema cae por M‑11, su
demostración suele estar bien: lo que hay que cambiar es el sujeto.*

Sólo hubo que escribir **tres** casos nuevos (`dne_rule`, `dne_schema`, `forall_not_ex_not`,
constructores desde D‑2), que son los únicos que piden lógica clásica en el metanivel
(`Classical.byContradiction`; ⚠️ sin Mathlib **no hay `by_contra`**). De ahí el `Classical.choice`
del footprint: legítimo y esperado, la semántica es clásica.

---

## 5 · VÍA H · Herbrand / disyunción finita

### 5.1 · El enunciado, y cuál es el que importa

    ⊢₀ ∃x̄ φ(x̄)   ⟺   ∃ t̄₁…t̄ₙ :  ⊢ᵖʳᵒᵖ  φ(t̄₁) ∨ … ∨ φ(t̄ₙ)        (φ sin cuantificadores)

⚠️ **Es un teorema sobre PROVABILIDAD, no sobre validez.** La versión «`⊨ ∃x̄φ` ⇒ disyunción»
vuelve a necesitar compacidad, o sea WKL. La de arriba es finitaria en las dos direcciones.

### 5.2 · Los cuatro hitos

| | hito | comentario | estado |
|---|---|---|---|
| **H1** | **semántica proposicional** para fórmulas sin cuantificadores: valuación booleana de los átomos | finitario, decidible | 🏁 **HECHO** 2026‑09‑16 |
| **H2** | **completitud proposicional para `Γ` FINITO** | tablas de verdad. Es la base y es honesta: aquí no hay König porque `Γ` es finito | 🏁 **HECHO** 2026‑09‑16 |
| **H3** | ⛔ **normalización / eliminación de cortes de `Derives₀`** | **la pieza grande.** Alternativa estándar: un secuentes `LK₀` sin corte, con `LK₀ → Derives₀` fácil y `Derives₀ → LK₀+corte`, y eliminar el corte allí | 🔶 **reducida a DOS `Prop`**: `CutElim` y `NDtoLK`, §5.5–§5.7 |
| **H4** | **extracción de testigos** de una prueba sin cortes | mecánico una vez está H3 | 🏁 **la mitad ⟸, HECHA** 2026‑09‑16 |

#### 🏁 H1 y H2, ejecutados (ADR‑042) — `../FOL/FOL/Propositional0.lean`, 244 l. de código

    derives0_of_ptaut     : PTaut φ → [] ⊢₀ φ
    derives0_of_ptaut_ctx : (∀ v, (∀ g ∈ Γ, peval v g) → peval v φ) → Γ ⊢₀ φ

⭐⭐ Footprint **`[propext, Quot.sound]`: ni un `Classical.choice`**, y `derives0_em_ctx`
(`Δ ⊢₀ A ∨ ¬A`) **no depende de ningún axioma**. *Aquí no hay König: `Γ` es finito y la valuación
recorre una lista finita de átomos.* Esto es finitario de verdad, no «reducible».

⭐ **Y una desviación del plan que lo mejora**: aquí decía «para fórmulas **sin cuantificadores**».
Tratar `∀` y `∃` **como átomos** —el *esqueleto proposicional*— no cuesta nada y hace el teorema
aplicable a **toda** fórmula. La restricción no lo habría hecho más fuerte, sólo menos útil.

⚠️ **No hay recíproca, y no puede haberla**: `⊢₀ φ` no implica `PTaut φ` — `(∀x P(x)) → P(t)` es
derivable y su esqueleto es `p → q`. *El cálculo sabe más que su esqueleto.*

⭐ **El control que mide para qué sirve la vía H**: `derives0_em` y `derives0_peirce` ya estaban
demostrados en `FOL.Canonical0` **por completitud semántica**, y arrastran `Classical.choice`.
Los mismos dos teoremas, por la vía H, son **net‑0**. *La vía H da lo mismo con footprint
estrictamente menor.*

⬜ **Y lo que falta es H3, que sigue siendo la pieza grande.** H1+H2 son la base, no el teorema.

### 5.4 · 🏁 H4 EJECUTADO (la mitad ⟸) y ⬜ H3 ENUNCIADA — 2026‑09‑16, ADR‑043

**Lo que hay** (`../FOL/FOL/Herbrand0.lean`, 154 l. de código, footprint `[propext, Quot.sound]`):

    derives0_ex_of_cert : HerbrandCert φ ts E → [] ⊢₀ ∃x φ(x)

⭐⭐ **El certificado es DATO SINTÁCTICO y se comprueba por CÓMPUTO**: `HerbrandCert φ ts E` son
una lista de términos, una lista de instancias de la igualdad (`EqInstance`, cerrada: refl,
simetría, transitividad, congruencia de función y de relación, **todas derivables**) y una
tautología proposicional del esqueleto — verificable con **`ptautCheck`, que reduce**, así que
sale `by rfl`. *Un certificado finito y verificable*, que es lo que §0 pedía del objetivo H.

⭐ **Y con eso, §5.3 queda resuelta en su forma finitaria.** La «clausura de congruencia» no se
implementa como procedimiento: **se convierte en un dato del certificado**. Ejemplo compilado:
`∃x (x ≐ c)` con `ts = [c]` y `E = [c ≐ c]` — su disyunción de Herbrand **no** es tautología
proposicional (es un átomo) pero sí es un axioma de la igualdad.

**Lo que falta, y está ENUNCIADO como `Prop`, no postulado:**

    HerbrandExtraction : ∀ φ, QuantFree φ → ([] ⊢₀ ∃x φ) → ∃ ts E, HerbrandCert φ ts E

con su **consumidor escrito**: `herbrand_iff (h3) : ([] ⊢₀ ∃x φ) ↔ ∃ ts E, HerbrandCert φ ts E`.
La mitad `←` es **incondicional**; `h3` sólo paga la `→`.

#### ⚠️ Por qué H3 no cae por inducción, dicho con precisión

⬜ **Análisis sobre la lista de constructores, no medición compilada** — y va etiquetado.

El enunciado de H3 **no es inductivo**. Ya el caso `intro_ex Γ φ t` pide que `φ(t)` se siga
**proposicionalmente** de instancias ecuacionales, y la hipótesis de inducción sólo da que es
*derivable*. Para que la inducción cierre hay que subir a un enunciado **sobre secuentes
arbitrarios** —el teorema del mid‑sequent—, y eso es exactamente la eliminación de cortes.

Y el obstáculo es contable. De los **21** constructores de `Derives₀`, **siete** son «de corte»
—tienen en una premisa una fórmula que **no aparece** en la conclusión, que es justo lo que un
Hauptsatz tiene que eliminar o permutar—:

| constructor | qué desaparece |
|---|---|
| `elim_impl` | `A` |
| `elim_and_l` · `elim_and_r` | `B` · `A` |
| `elim_or` | `A` y `B` |
| `elim_ex` | `A` |
| ⛔ `subst` | `t₁` — **y es la regla de la IGUALDAD** |
| ⛔ `rewrite_at` | `sub`, `sub'` y la posición `p` — **regla no estándar de este cálculo** |

más `weakening`, que es estructural. ⚠️ Los dos marcados ⛔ son los que hacen que esto **no** sea
un Hauptsatz de libro: `subst` es Leibniz —la igualdad no se elimina, se vuelve teoría— y
`rewrite_at` no tiene análogo en LK.

⇒ ⬜ **La vía sensata sigue siendo la del §5.2**: definir `LK₀` sin corte, probar
`LK₀ → Derives₀` (fácil) y `Derives₀ → LK₀ + corte`, y eliminar el corte allí. ⛔ **No se ha
empezado a propósito**: diseñar `LK₀` sin poder validarlo contra la mitad difícil es fabricar una
obligación que puede salir inconsumible — el escarmiento está escrito
(`feedback_enunciar_una_deuda`: *la guarda se copia del CONSUMIDOR, no del molde*).

---

### 5.5 · 🏁 H3, primera pieza: **`rewrite_at` RETIRADA** — 2026‑09‑16, ADR‑044

§5.4 dejó el obstáculo **contado**: siete constructores «de corte», y **dos** que impedían que
esto fuera un Hauptsatz de libro — `subst` (Leibniz) y ⛔ `rewrite_at` (sin análogo en LK).

**Uno de los dos ya no está** (`../FOL/FOL/Derives1.lean`, 214 l. de código,
footprint `[propext, Quot.sound]`):

    Derives₁               -- los 20 ctors de `Derives₀` MENOS `rewrite_at`
    derives0_iff_derives1  -- y derivan EXACTAMENTE lo mismo

⇒ **`Derives₁` es deducción natural clásica de libro más igualdad.** El frente de H3 pasa de
**dos** obstáculos a **uno**. ⭐ Y `Derives₁.rec` **no depende de ningún axioma** (`Derives₀.rec`
lleva `propext`).

⭐ **Cómo se retira**: `LocalRule` tiene **un solo** constructor (`commuteImpl`), así que la
eliminación es una **congruencia por posiciones**. ⚠️ Y tiene que ser **biconditional** aunque
`rewrite_at` sólo pida una dirección: al bajar por el **antecedente** de una implicación la
congruencia se **invierte**, así que la inducción necesita las dos mitades a la vez.

⭐ Los dos casos caros —`Pos.body`, bajo el binder— salen por `intro_forall` (que levanta el
contexto) y `elim_forall` con `Term.var 0`, cerrando con **`substFormula_lift_var`**: *el mismo
lema que sostenía el paso de eigenvariable de Henkin* (ADR‑036). Salió gratis porque ya estaba.

⚠️ **Y una medición que cambia el diseño del siguiente paso**: `getAt?` y `replaceAt` se compilan
por recursión **bien fundada** (sus llamadas cambian los **dos** argumentos), así que **no
reducen** — `getAt? f .root = some f` **no es `rfl`**. Hay que ir por sus ecuaciones. Es primo de
⛔ *los símbolos OBJETO no reducen*, pero por otra causa: el símbolo es de Lean y lo que falla es
el **esquema de recursión**.

#### ⬜ El obstáculo que queda, y lo que se ha MEDIDO de él

`subst` — Leibniz. La vía estándar es reducirlo a **instancias de congruencia**, dejando el
cálculo en ND puro + axiomas de igualdad, que es como la literatura enuncia Herbrand con `=`.

⚠️⚠️ **Pero hay un dato medido que obliga a hacerlo en el orden correcto**: las cuatro piezas de
`FOL/Eq0.lean` —simetría, transitividad y las dos congruencias de una posición— están **derivadas
DE `subst`** (`Derives₀.subst` aparece en las cuatro). ⇒ **no se puede quitar `subst` y conservar
las congruencias como teoremas**: hay que **subirlas a constructores primitivos** y luego probar
que `subst` es admisible a partir de ellas.

⬜ **Estimación etiquetada, no medida**: `Derives₂` (20 ctors − `subst` + 2 congruencias) ~60 l.
de andamiaje, Leibniz a nivel de **término** ~100 l., a nivel de **fórmula** ~150 l. (⚠️ el caso
del binder cambia el índice de sustitución y levanta el término: `substFormula 0 t (∀a) =
∀ (substFormula 1 (liftTerm 0 t) a)`), más las dos traducciones ~80 l. **Riesgo medio‑alto**, y
concentrado en el caso del binder.

---

### 5.6 · 🏁 H3, segunda pieza: **`subst` RETIRADA** — 2026‑09‑16, ADR‑045

    Derives₂               -- `Derives₁` SIN `subst`, con TRES congruencias primitivas
    eq_substFormula        -- ⭐⭐ Leibniz, DEMOSTRADO a partir de ellas
    derives0_iff_derives2  -- y deriva EXACTAMENTE lo mismo que el cálculo original

`../FOL/FOL/Derives2.lean`, **347 l. de código**, `[propext, Quot.sound]` — **ni un
`Classical.choice`**; ⭐ `Derives₂.rec` **sin ningún axioma**.

⇒ 🏁🏁 **Los DOS obstáculos que §5.4 había contado ya no están.** `Derives₂` es **deducción
natural clásica de libro más los axiomas de la igualdad** — exactamente la forma en que la
literatura enuncia Herbrand con `=`. Y lo que queda «de corte» son los **cinco estándar**
(`elim_impl`, `elim_and_l/r`, `elim_or`, `elim_ex`), que es de lo que trata Gentzen.

⭐ **Y con esto §5.3 queda cerrada del todo.** Aquella sección decía que la igualdad obligaba a una
«capa entera más» de clausura de congruencia. Medido: son **tres constructores** —congruencia de
función, de relación y de `≐`— y con ellos Leibniz **se demuestra**. La igualdad deja de ser una
regla de inferencia y pasa a ser **teoría**, que es lo que hacía falta para que el Hauptsatz se
pueda plantear.

⚠️ **Simetría y transitividad no hacen falta como primitivas**: salen de `eq_eq_congr` + `refl`.
Pero `eq_eq_congr` **sí**, porque `Formula.eq` es un constructor propio y no un `atom`.

⭐ **Dónde está el trabajo**: en dos escalones. (1) Leibniz de **términos**, donde hay que subir de
igualdades **punto a punto** de la lista de argumentos a la igualdad de los términos — *lo que
falta no es lógica sino LISTAS*, otra vez (ADR‑031). (2) Leibniz de **fórmulas**, donde ⛔ los
casos `∀`/`∃` obligan a que la ecuación **viaje al contexto levantado**, porque la sustitución
**cambia de índice y levanta el término**. De ahí `derives2_lift`, una inducción entera sobre los
22 constructores y la mitad del coste del módulo.

⭐ Y un contraste con §5.5 que vale la pena: allí `impl` obligó a un enunciado **bicondicional**;
aquí no, porque el enunciado **ya es simétrico en `t₁`/`t₂`** y basta aplicar la hipótesis de
inducción con los términos intercambiados. *Cuando la simetría está en los datos, no hay que
meterla en el enunciado.*

#### ⬜ Lo que queda de H3: **el Hauptsatz**, y ya sin excusas de forma

El cálculo está en la forma estándar. ⬜ Sigue faltando la eliminación de cortes —y con ella la
extracción del certificado (`HerbrandExtraction`)—, que es **la pieza grande** y ahora es un
problema de libro y no de este cálculo en particular.

---

### 5.7 · 🏁 H3, tercera pieza: **el cálculo de secuentes**, y la deuda reducida a DOS — ADR‑046

    LK₀                    -- secuentes clásicos de dos lados, SIN corte (13 ctors)
    LKc                    -- lo mismo MÁS el corte (14)
    lk0_herbrand           -- ⭐⭐ la EXTRACCIÓN: de `LK₀ E ⟹ ∃xφ` salen los términos
    herbrandExtraction_of  -- ⭐⭐⭐ CutElim + NDtoLK ⇒ H3

`../FOL/FOL/Sequent0.lean`, **348 l. de código**. `lk0_herbrand` mide **`[propext]`**,
`lk0_to_lkc` **ningún axioma**, y la cadena `[propext, Quot.sound]` — **ni un `Classical.choice`**.

⭐ **El orden importa y es el que ADR‑043 §3 había decidido**: no construir el molde sin
consumidor. El consumidor apareció en ADR‑043 (`HerbrandCert`) y el cálculo quedó en forma estándar
en ADR‑045; **sólo entonces** se construye `LK₀`, y **lo primero que se hace con él es probar el
consumidor**. Si `lk0_herbrand` no hubiera salido, el diseño estaría mal y no se sabría hasta el
Hauptsatz.

⭐⭐ **Y lo que `lk0_herbrand` enseña de paso**: de sus 13 casos, **uno** produce el testigo
(`exR`), **tres son imposibles** (`allR`, `allL`, `exL`: meten un cuantificador donde no puede
haberlo) y **nueve** son bookkeeping proposicional. 🔑 *La regla de corte tendría una fórmula
arbitraria que no aparece en la conclusión, así que las hipótesis de la inducción no se heredan:
el corte es exactamente lo que rompe esta lectura.* Ahí está, en una frase, para qué sirve el
Hauptsatz.

#### ⬜ Lo que queda de H3: **dos `Prop`, y nada más**

    CutElim : ∀ Γ Δ, LKc Γ Δ → LK₀ Γ Δ                      -- el HAUPTSATZ
    NDtoLK  : ∀ Γ f, Derives₂ Γ f →
                ∃ E, (∀ g ∈ E, EqInstance g) ∧ LKc (E ++ Γ) [f]

⚠️ **`NDtoLK` no es rutina, y su dificultad está localizada** (⬜ medida como problema, no como
coste): el caso `intro_forall` **levanta el contexto**, así que la lista `E` que devuelve la
hipótesis de inducción vive en el contexto **levantado**, y hay que producirla desde el de abajo —
pero una instancia con `Term.var 0` no es el levantamiento de ninguna.

⚠️ **Y una comprobación que NO está hecha**: `LK₀ Γ Δ → Derives₂ Γ (disjOf Δ)`, es decir, que `LK₀`
no sea **demasiado fuerte**. ⬜ El obstáculo está identificado: el caso `allR` exige sacar una
disyunción de dentro de un cuantificador (`∀x(A ∨ C) → (∀x A) ∨ C` con `C` sin `x`). No está en el
camino crítico —las dos obligaciones de arriba no pasan por ella—, pero es lo que certificaría que
el molde no prueba de más.

---

### 5.3 · ⚠️ Y lo que cuesta la IGUALDAD, que aquí sí cuesta

Sin `=`, la disyunción de Herbrand termina en **tautología proposicional**. Con `=`, termina en
tautología **ecuacional de términos cerrados** ⇒ hace falta **clausura de congruencia**
(Ackermann / Nelson–Oppen): decidible y finitaria, pero es una **capa entera más**.

⚠️ **No es opcional**: Q es una teoría con igualdad. Sin `=` no hay `S(x)=S(y) → x=y`, ni
representabilidad, ni cadena de Gödel.

⭐ **Dato medido hoy que conviene tener delante**: quitar la igualdad **no** ahorraría nada del
lado de Henkin. El experimento natural está en `../FOL/cuarentena/librerias-retiradas/`:

| librería | `=` | ∀∃ | `henkin_extension_lemma` | `termEqv_*_congr` |
|---|---|---|---|---|
| `FOL_poli` (= FOL⁼) | ✅ | ✅ | **sí** | **sí** (2) |
| `FOLPure` (sin `=`) | ❌ | ✅ | **sí** | — |
| `PropLogic` | ❌ | ❌ | **no** | — |

⇒ **la igualdad añade el cociente; los cuantificadores añaden Henkin.** Son costes distintos y
ninguno de los dos es el núcleo no finitario.

---

## 6 · VÍA W · Completitud para `Γ` numerable/r.e., y su reducción declarada

### 6.1 · Lo que ya está

Casi todo. `cuarentena/Completeness.lean` porta a `Derives₀` **sin tocar nada sustancial**
⬜ (estimación, no medida — pero apoyada en que usa 14 constructores y ninguno es `gen_rule`, y en
que ni importa `MetaRules`):

* `lindenbaum_lemma` ✅ incondicional
* modelo canónico y `truth_lemma` ✅ net‑0
* `formula_enum` ✅ construido y **computable**
* congruencias de la igualdad ✅ teoremas

### 6.2 · Lo que hay que rehacer: **Henkin, de verdad**

Con `raa` fuera, `derives_complete` desaparece y la demostración de ADR‑032 **ya no vale**. Hay
que hacer la construcción clásica:

1. `S₁ := S ∪ { (∃A) → A[c_A] }` con testigos frescos, iterado ω veces.
2. La consistencia de cada paso se prueba por **contraposición**, y ahí hace falta el
   **lema de renombrado sobre derivaciones** (`Γ ⊢₀ φ → ρΓ ⊢₀ ρφ`) — es **inducción sobre la
   derivación**, ⭐ **desbloqueada por el Paso 0**.
   🏁 **HECHO el 2026‑09‑14** (ADR‑035): `../FOL/FOL/Rename.lean`, `derives0_rename`, footprint
   **`[propext, Quot.sound]`** — *ni siquiera `Classical.choice`*: el renombrado es **puramente
   constructivo**. Los 21 casos, más las conmutaciones con `lift`, `subst`, `getAt?`, `replaceAt`
   y `LocalRule`. ⭐ Salió barato porque **el renombrado no toca las variables**, así que conmuta
   con todo; y porque `LocalRule` tiene **un solo constructor**.
   🏁 **Y la recíproca también** (`derives0_rename_inv`, mismo footprint `[propext, Quot.sound]`):
   sale de aplicar el lema directo **a la inversa**, cuatro líneas y cero casos. ⭐ La
   conservatividad **no necesita elección**; la necesita sólo el paso «inyectiva ⇒ tiene inversa».
   🏁 **Y el paso de EIGENVARIABLE, el mismo día** (ADR‑036, `../FOL/FOL/Eigenvariable.lean`):
   `derives0_gen_fresh (c) (hfresh : ∀ g ∈ Γ, ¬ occursFormula c g) : Γ ⊢₀ φ → Γ ⊢₀ ∀ (absFormula c 0 φ)`,
   footprint **`[propext, Quot.sound]`**. ⚠️ Ésta **sí** toca los índices, así que sus conmutaciones
   llevan hipótesis de nivel (`j ≤ k`, `v ≤ k`) y el `∀ k` va **dentro** del motivo de la
   inducción. ⭐ Encaja porque `intro_forall` **ya es** la eigenvariable en De Bruijn: lo único que
   faltaba era el puente `absFormula_eq_lift` —*si `c` no aparece, abstraerla ES levantar*.

⇒ 🏁 **Las tres piezas de §6.2 están** — y el ensamblaje descubrió una cuarta, `derives0_lift`
(`../FOL/FOL/Lift0.lean`), porque `∃A` contra `∀¬A` pasa por `elim_ex` y su premisa vive en el
contexto **levantado**.

🏁🏁 **Y el CORAZÓN del ensamblaje está probado** (ADR‑037, `../FOL/FOL/Henkin0.lean`):

    henkin_step_consistent : IsConsistent₀ S → (c fresca en S y en A) →
        IsConsistent₀ (S ∪ { (∃A) → A[c] })

⭐ **El punto fino**: `derives0_gen_fresh` pide `c` fresca en el **contexto finito**, y `⊢₀*`
—«existe un `Γ` FINITO dentro de `S`»— entrega exactamente eso. *La compacidad sintáctica metida
en la definición es lo que abarata el paso.*

### 6.4 · 📏 Lo que queda, MEDIDO (2026‑09‑14)

⚠️⚠️ **Corrección**: aquí decía que el suministro de nombres era «combinatoria de nombres» y el
trozo **caro**. **Medido, es barato** — `sondeos/NombresFrescosMedicion.lean`.

**MEDIDO** (compilando):

| pieza | medición |
|---|---|
| `ρ s := "f" ++ s` inyectiva | `String.append_right_inj` **existe**; `rho_inj` sale **limpio** `[propext, Quot.sound]` |
| constantes fuera de la imagen | `"g" ++ t ≠ "f" ++ s` **compila por `rfl` sobre `beq`** (⚠️ verificado con control adversarial) |
| familia infinita e inyectiva | `cst : Nat → String`, **3 líneas** |
| ⛔ inversa computable de `++` | **NO existe** (`String.drop` da un `Slice`) — y **no hace falta**: la conservatividad pide inyectividad |
| bloque Lindenbaum análogo | **110 líneas**; 10 usos de constructores, **todos presentes en `Derives₀`**; **cero** dependencias fuera del núcleo |
| bloque `max_cons_*` | **121 líneas**, ídem |
| bloque `DerivesSet_*` | **61 líneas** |
| `cuarentena/Completeness.lean` entero | **801 líneas** |

**ESTIMADO** ⬜ (y va etiquetado, que es la regla) — **con lo REAL al lado, medido el 2026‑09‑16**:

| ítem | estimación | riesgo | 📏 real (código) |
|---|---|---|---|
| (1) suministro de frescas | ~**80** líneas | **bajo** — las dos piezas duras están medidas | 🏁 **150** (`FOL/Fresh0.lean`) |
| (2) iteración ω | ~**190** líneas | ⚠️ **medio** — ver abajo | 🏁 **168** (`FOL/HenkinLimit0.lean`) |
| (3) Lindenbaum sobre `Derives₀` + `IsHenkin` del límite | ~**200** líneas | **bajo** — calco medido | 🏁 **126** (`FOL/Lindenbaum0.lean`) |
| **⇒ ensamblaje de Henkin** | ~**470** líneas | | 🏁🏁 **444**, COMPLETO |
| resto de la vía W (modelo canónico + `truth_lemma` + `completeness`) | ~**470** líneas | **bajo** — es lo que queda de las 801, y no usa nada fuera de `Derives₀` | 🏁 **510** (`FOL/Eq0.lean` + `FOL/Canonical0.lean`) |

🏁🏁🏁 **LAS TRES EJECUTADAS el 2026‑09‑16** (ADR‑039 y ADR‑040). El **ensamblaje de Henkin está
CERRADO**:

    henkin_completion : IsConsistent₀ S →
      ∃ T, IsMaximalConsistent₀ T ∧ IsHenkin₀ T ∧ (∀ f, shiftTheory S f → T f)

y por debajo, la extensión de Henkin construida:

    henLimit_consistent : IsConsistent₀ S → IsConsistent₀ (henLimit S)
    henLimit_witness    : ∀ A, ∃ c, henLimit S (henkinAx c A)

footprint `[propext, Classical.choice, Quot.sound]`, **cero axiomas del proyecto**.

⚠️⚠️ **Y el riesgo de (2) se disolvió — corrección de este documento.** Aquí decía:

> ⚠️ **El riesgo de (2), localizado**: `cₙ` tiene que ser fresca para `Sₙ ∪ {φₙ}`, y `φₙ` recorre
> **todas** las fórmulas — puede usar cualquier `cst m`. ⇒ no vale «`cₙ := cst n`»: hay que elegir
> `cₙ := cst (1 + máximo índice usado en φₙ y en los axiomas ya añadidos)`. Eso pide una función
> `Formula → Nat` («mayor índice de `cst` que aparece») y su lema, ~40 líneas. **Está identificado,
> no medido.**

**El diagnóstico era correcto; la solución cotizada, no.** Esa función **no hace falta**. El
enunciado que la iteración consume no es «el máximo índice» sino «**a partir de cierto índice,
todas son frescas**»:

    cst_bound_formula : ∀ f, ∃ N, ∀ m ≥ N, ¬ occursFormula (cst m) f

que sale por inducción estructural con `max`, **sin invertir `cst` y sin tocar `String.length`**;
el único paso clásico está en el **símbolo** (`Classical.em (∃ k, cst k = s)` más `cst_inj`). Y
`Exists.choose` lo convierte en la función `bnd` con la que se define el índice del turno:

    hidx 0 := bnd (natToFormula 0)   ·   hidx (n+1) := max (hidx n + 1) (bnd (natToFormula (n+1)))

estrictamente creciente (⇒ testigos distintos) y dominando las cotas anteriores (⇒ frescura).

🔑 **La lección**: el plan cotizó *la solución que se le ocurrió*, no *el problema*. Un `∃` bien
elegido puede sustituir a una función y a su lema. ⇒ **van seis** estimaciones mías refutadas por
una medición, y ésta hacia **abajo**.

⚠️ Y lo que **sí** se sostiene de la afirmación vieja: el suministro mete `Classical.choice` en el
footprint — pero por la **implementación** de `String` (§7), no por la matemática.
⚠️ Y ahí reaparecerá `String` (§7): el renombrado concreto necesita **descomponer cadenas** para su
inversa, y eso trae `Classical.choice`. Las tres piezas son constructivas; el ensamblaje no lo será
mientras los símbolos sean `String`.
3. ⭐ Y sobrevive intacta la pieza limpia que ya está medida:
   `no_instance_no_body` (`sondeos/HenkinSaleDeRaa.lean`, footprint **`[propext]`**, sólo
   `intro_forall` + `elim_forall`). `Derives.intro_forall` **es la regla de la eigenvariable
   incorporada**, así que ⬜ **puede que baste con variables frescas y el lifting, sin ampliar el
   lenguaje con constantes**. *Estimación, no medida — y con antecedentes: el juicio «amplía el
   lenguaje con constantes» ya resultó falso una vez (ADR‑032).*

### 6.3 · Lo que NO se quita, y hay que escribirlo en vez de pelearlo

El `if IsConsistent (S_n ∪ {φ_n})` de `LindenbaumStep` es **Π⁰₁** y se resuelve por
`Classical.propDecidable`. **Ahí cabe toda la no‑finitud del teorema.**

🏁 **Escrito el 2026‑09‑16** — `FOL/Lindenbaum0.lean`, `LindenbaumStep`, y está **señalado en el
sitio**: en el docstring del módulo, en el de la `def` y en ADR‑040 §2.

⚠️⚠️ **Y de ahí sale la obligación de leer los footprints con cuidado.** `Classical.choice`
aparece ya en tres módulos del ensamblaje por **tres causas distintas**:

| dónde | causa | ¿matemática? |
|---|---|---|
| `FOL.Fresh0` | `Classical.em` sobre `∃ k, cst k = s`, y `String` | parcialmente — la de `String` es del núcleo |
| `FOL.HenkinLimit0` | `Exists.choose` en `bnd` | no: es elegir un testigo que existe |
| `FOL.Lindenbaum0` | ⛔ **el `if IsConsistent₀ …`, Π⁰₁** | ⛔ **SÍ. Es el WKL.** |

🔑 **El footprint no distingue las causas, así que hay que distinguirlas por escrito.**

⇒ El entregable de W **no es un footprint limpio**, es:

* `completeness₀ : Γ ⊨ f → Derives₀ Γ f` con footprint
  `[propext, Classical.choice, Quot.sound]` y **cero axiomas del proyecto**; y
* la **nota de reducción** al lado: *ese `Classical.choice` es el WKL, ≡ completitud sobre RCA₀,
  y WKL₀ es Π⁰₂‑conservativo sobre PRA.*

🔑 **Un `Classical.choice` explicado vale más que un `Classical.choice` escondido.**

---

## 7 · ⛔ El muro constructivo, medido el 2026‑09‑14: **`String`**

Si en algún momento se quiere ir más allá de «reducible» hacia «constructivo», el obstáculo **no
es un axioma**. Censo con `collectAxioms` (`sondeos/ClassicalChoiceCenso.lean`):

* **FOL 16 / 411** y **FOL+RPP 3 143 / 5 045 (62 %)** llevan `Classical.choice`.
* En Lean v4.31 **toda operación que DESCOMPONE un `String` lo trae** (`toList`, `data`, `foldr`,
  `foldl`, `length`, `get`); construirla o compararla, **no** (`ofList`, `decEq`).
* La raíz en RPP son **dos líneas**: `strCode s := charsCode s.toList` y `strCodeM`. `charsCode`,
  `numeralM` y `axiomsCodeT` están **limpios**.

🔑 **El footprint no distingue la no‑constructividad MATEMÁTICA de la deuda de IMPLEMENTACIÓN del
núcleo.** `strCode` es computable y constructiva.

⬜ **Si se quisiera de verdad**: cambiar `Term.func : String → List Term → Term` por un tipo de
símbolos **numerable y con `DecidableEq` real**. Limpiaría también las 6 de
`FOL/Enumeration.lean`. **Es un cambio de firma en FOL y toca a RPP entero.**

---

## 7.2 · ¿Por qué sustituirlo, y por qué? — análisis de **btw**, con su medición pendiente HECHA

> ⚠️ Recogido aquí a petición del propietario. El análisis es de **btw**; lo que va marcado como
> **MEDIDO el 2026‑09‑14** lo añade este documento, y es justamente la medición que el propio
> análisis declaraba pendiente. Artefacto: `sondeos/SimbolosSinString.lean`.

### El arreglo es más quirúrgico de lo que sugiere el 62 %

Lo medido es que **`charsCode : List Char → Term` no depende de ningún axioma**, y que
`strCode s := charsCode s.toList`. Es decir: **toda la cadena de Gödel está a una composición de
estar limpia.** El problema no es la codificación: es **leer el `String`**.

### Los tres candidatos

| candidato | a favor | en contra |
|---|---|---|
| **`List Char`** | el **mínimo cambio**: `strCode` se convierte **literalmente en `charsCode`**, que ya está medido limpio. La descomposición es gratis (es un inductivo). Conserva la legibilidad si se añade una macro `sym!"succ"` que expanda en elaboración a `['s','u','c','c']` — el término resultante no menciona `String.toList`, así que no arrastra nada | — |
| **`Nat`** | máximamente primitivo y **garantizado limpio** (`numeralM` y `axiomsCodeT` ya lo están); la codificación se vuelve trivial | ⚠️ los literales del corpus pasan a ser **números**, y sin una capa de `abbrev` por símbolo el libro y los mensajes de error se vuelven **ilegibles** |
| **`Sym : Type` abstracto** con `[DecidableEq Sym]` y numerabilidad | lo principista, y hay **precedente** (el enhebrado de `AnclaEq` por ~440 firmas con el bucle build→anotar) | toca los **131 módulos** |

### Lo que el tipo de símbolos tiene que cumplir

| requisito | por qué |
|---|---|
| `DecidableEq` limpio | el `filter` de Henkin, la distinción de códigos |
| **infinito numerable** | ⛔ Henkin necesita **infinitas constantes frescas** |
| codificación limpia a `Term` | la cadena de Gödel |
| literales legibles | el corpus y el libro |

⚠️ **El segundo descarta un alfabeto finito** (`inductive Sym | zero | succ | …`), que sería lo más
limpio de todo: **sin constantes frescas no hay extensión de Henkin.**

### 📏 La medición que faltaba — HECHA, y sale LIMPIA

El análisis decía: *«`Char` no está verificado del todo… Si eso arrastrara choice, `List Char`
pierde la gracia. Es una medición de tres líneas, pero no está hecha.»*

**MEDIDO el 2026‑09‑14** (`sondeos/SimbolosSinString.lean`, compilado):

| constante | footprint |
|---|---|
| `Char` · `Char.val` · `Char.ofNat` · `Char.toNat` | **sin axiomas** |
| `Char.ofNat_toNat` · `Char.isValidCharNat` | **sin axiomas** |
| `instDecidableEqChar` | **sin axiomas** |
| `DecidableEq (List Char)` | **sin axiomas** |
| `charsCode` | **sin axiomas** |
| ⛔ `strCode` · `String.toList` | `[propext, Classical.choice, Quot.sound]` |

⇒ ⭐ **La recomendación queda confirmada**: `List Char` cumple los cuatro requisitos, y **`String`
es lo único sucio de la cadena**.

### ⬜ Lo que sigue sin medir, y el riesgo

* **La propagación real.** El proyecto tiene el escarmiento escrito: el cierre por nombres
  **sobreestimó por dos órdenes de magnitud**; sólo el compilador vale. **No medido.**
* ⚠️ **Cambia `G`.** Al cambiar la representación de los símbolos cambia `strCode`, y con él
  `formCode`, `axiomsCodeT`, `provCodeC'` y **la sentencia de Gödel**. Los teoremas son
  paramétricos en eso y *deberían* sobrevivir, pero hay muchos **puentes por `rfl`** y
  comparaciones de códigos que habría que re‑verificar **uno a uno**. 🔑 *Estimación, etiquetada.*
* ⭐ **A cambio se simplifican las piezas más feas**: `CodeDistinct` y `codeNatChars_inj` usan hoy
  `String.toList_inj` y `String.ext`; **con listas, la inyectividad es gratis**.

### La lectura, y por qué NO es urgente

**`List Char` es la apuesta correcta** —y la medición que la condicionaba sale limpia—: mantiene la
legibilidad, convierte **dos `def` en uno que ya existe**, y no toca la estructura del lenguaje.

⚠️ **Y no es urgente**: es una decisión de esta §7, y **sólo cambia lo que el footprint DICE, no lo
que el proyecto ha demostrado**. `strCode` ya es computable y constructiva hoy — es
**la regla** de que el footprint no distingue la no‑constructividad matemática de la deuda de
implementación del núcleo.

### 7.3 · ✅ Decisión: **PROYECTADO**, no pendiente (2026‑09‑14)

Sanción del propietario: *«lo proyectamos para cuando termines el trabajo más inmediato y todo esté
más limpio»*.

⇒ ⛔ **Esto NO es trabajo pendiente y no debe aparecer como tal.** Es una migración **decidida en
principio** (`List Char`, confirmada por medición) y **aplazada a propósito**, con dos condiciones
explícitas:

| condición | estado |
|---|---|
| cerrar el **trabajo inmediato** — el ensamblaje de Henkin (§6.4) y la vía W | ⬜ en curso |
| que el árbol esté **más limpio** | ⬜ |

⚠️ **Y una razón técnica para que sea en ese orden, no en otro**: la migración **cambia `G`**
(§7.2), así que hacerla **en medio** del ensamblaje obligaría a re‑verificar los puentes por `rfl`
**dos veces**. Primero se cierra, después se migra.

🔑 Lo que se gana esperando no es comodidad: es **no pagar dos veces la misma re‑verificación**.

---

## 8 · Orden de trabajo, y qué NO hacer

| | | depende de |
|---|---|---|
| ~~**1**~~ | 🏁 ~~`Derives₀` + encaje a `Derives` (§3)~~ — **HECHO 2026‑09‑14** | — |
| ~~**2**~~ | 🏁 ~~`derives0_soundness` (§4)~~ — **HECHO 2026‑09‑14** | 1 |
| **3** | portar `Completeness.lean` a `Derives₀` y **medir qué se rompe** | 1 |
| **4** | H1 + H2 (proposicional finito) | 1 |
| **5** | Henkin real (§6.2) | 1, 2 |
| **6** | ⛔ H3, normalización | 1 |
| **7** | H4 + la capa de congruencia con `=` (§5.3) | 6 |

⛔ **Lo que NO hay que hacer:**

* **No pagar `henkin_extension_lemma` en `Derives`.** Decidido (ADR‑032, opción A); para tocarlo
  hay que reabrir el ADR, y `check-axioms.bash` (`ESPERADO_CUAR=1`) rompe también si baja a 0.
* **No perseguir un footprint sin `Classical.choice` en la vía W.** Es el teorema, no la
  formalización (§6.3).
* **No tocar las 320 citas de las meta‑reglas en RPP.** `Derives₀` es un objeto nuevo (§3.4).
* **No inducir sobre `Derives`.** M‑11 es permanente (ADR‑029): suelo de cuatro.

---

## 9 · Criterios de aceptación (cómo se mide cada hito)

| hito | verde cuando |
|---|---|
| §3 | 🏁 **CUMPLIDO**: `Derives₀` compila y `Derives₀.rec` mide `[propext]` — ningún axioma del proyecto |
| §4 | 🏁 **CUMPLIDO del todo**: `derives0_soundness` mide `[propext, Classical.choice, Quot.sound]` —cero axiomas del proyecto— **y `check-footprints.bash` lo reejecuta** (13 titulares, en CI, probado con el fallo puesto) |
| §6 | `completeness₀` con footprint `[propext, Classical.choice, Quot.sound]` y **cero** axiomas propios, con la nota de reducción escrita al lado |
| §5 | Herbrand con footprint **sin `Classical.choice`** para el fragmento sin `=`; con `=`, la capa de congruencia declarada aparte |

⚠️ Y el de siempre: **un verde no es haber comprobado**. Cada hito entra con su control, y el
control se prueba **con el fallo puesto**.

⭐ **El control de esta columna ya existe**: `check-footprints.bash` (raíz de RPP, en el `Makefile`
como `make footprints` y en CI). Compara **13 titulares** de los dos repos con su footprint
publicado y **rompe** si no cuadra. Probado en los dos modos de fallo: footprint distinto
(`✗ … dice […], esperado […]`) y declaración ausente (`✗ … NO MEDIDO`), los dos con `EXIT=1`.
🔑 *Un `info:` en medio de 145 jobs no es un control: nadie lo lee y, si cambia, no rompe nada.*

---

**Véase también:** `DECISIONS.md` ADR‑024 (M‑10), ADR‑029 (M‑11 permanente), ADR‑030, ADR‑031,
ADR‑032 · `sondeos/HenkinSaleDeRaa.lean` · `sondeos/ClassicalChoiceCenso.lean` ·
`sondeos/AnclaSoundness.lean` · `../FOL/AXIOMS.md` · `../FOL/cuarentena/README.md`.

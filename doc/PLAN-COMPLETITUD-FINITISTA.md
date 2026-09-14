# PLAN-COMPLETITUD-FINITISTA.md — dos objetivos, un bloqueante común

**Última actualización:** 2026-09-14 · **Autor:** Julián Calderón Almendros

> 🏁🏁 **PASOS 0 y 1 EJECUTADOS el 2026‑09‑14** (ADR‑033, ADR‑034). `Derives₀` está en el build
> (`Derives₀.rec` mide `[propext]`) **y su SOLIDEZ está demostrada**:
> `derives0_soundness : Γ ⊢₀ f → Γ ⊨ f`, footprint `[propext, Classical.choice, Quot.sound]` —
> **cero axiomas del proyecto**.
> ⭐⭐ Con ella salen **`derives0_consistent`** (la primera consistencia de un cálculo de FOL⁼ en
> el proyecto) y **`derives0_not_complete`** (`Derives₀` **no** decide toda fórmula ⇒ el Paso 0
> sirvió para lo que tenía que servir). ⭐ Y RPP **no se movió**: sigue en 145 jobs.

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

| | hito | comentario |
|---|---|---|
| **H1** | **semántica proposicional** para fórmulas sin cuantificadores: valuación booleana de los átomos | finitario, decidible |
| **H2** | **completitud proposicional para `Γ` FINITO** | tablas de verdad. Es la base y es honesta: aquí no hay König porque `Γ` es finito |
| **H3** | ⛔ **normalización / eliminación de cortes de `Derives₀`** | **la pieza grande.** Alternativa estándar: un secuentes `LK₀` sin corte, con `LK₀ → Derives₀` fácil y `Derives₀ → LK₀+corte`, y eliminar el corte allí |
| **H4** | **extracción de testigos** de una prueba sin cortes | mecánico una vez está H3 |

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
   ⬜ **Pero esto NO es todavía Henkin**: falta el paso de **eigenvariable** —de `Γ ⊢₀ φ(c)` con `c`
   fresca concluir `Γ ⊢₀ ∀x φ(x)`—, que **no es un renombrado** (manda una constante a una
   **variable**, con corrimiento de índices). Otra operación, `abstractConst`, y otra inducción; y
   ⚠️ **más cara**, porque **sí toca las variables**.
3. ⭐ Y sobrevive intacta la pieza limpia que ya está medida:
   `no_instance_no_body` (`sondeos/HenkinSaleDeRaa.lean`, footprint **`[propext]`**, sólo
   `intro_forall` + `elim_forall`). `Derives.intro_forall` **es la regla de la eigenvariable
   incorporada**, así que ⬜ **puede que baste con variables frescas y el lifting, sin ampliar el
   lenguaje con constantes**. *Estimación, no medida — y con antecedentes: el juicio «amplía el
   lenguaje con constantes» ya resultó falso una vez (ADR‑032).*

### 6.3 · Lo que NO se quita, y hay que escribirlo en vez de pelearlo

El `if IsConsistent (S_n ∪ {φ_n})` de `LindenbaumStep` es **Π⁰₁** y se resuelve por
`Classical.propDecidable`. **Ahí cabe toda la no‑finitud del teorema.**

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
símbolos **numerable y con `DecidableEq` real** (`Nat`). Limpiaría también las 6 de
`FOL/Enumeration.lean`. **Es un cambio de firma en FOL y toca a RPP entero: no está planificado
aquí.**

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

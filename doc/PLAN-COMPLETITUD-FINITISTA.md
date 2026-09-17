# PLAN-COMPLETITUD-FINITISTA.md — dos objetivos, un bloqueante común

**Última actualización:** 2026-09-18 01:20 · **Autor:** Julián Calderón Almendros

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
> # 🏁🏁🏁 **VÍA H CERRADA — 2026‑09‑17** (ADR‑050, ADR‑051, ADR‑052)
>
> ```
> hauptsatz : CutAdm                                       -- el corte es ADMISIBLE en LK₀
> herbrand  : ([] ⊢₀ ∃φ) ↔ ∃ ts E, HerbrandCert φ ts E      -- Herbrand, ya INCONDICIONAL
> ```
>
> `FOL/Hauptsatz0.lean`, footprint `[propext, Quot.sound]`: **ni un `Classical.choice`, ni un axioma
> del proyecto**. ⇒ **los DOS objetivos de este plan están cerrados**, y los cuatro hitos de §5.2
> con ellos. Ver §5.11.
>
> ⭐ **Y el dividendo que justifica el precio**: `derives0_consistent_fin`, la consistencia de
> `Derives₀` por la vía **sintáctica** (`ndToLK` + `cut_elimination` + evaluación booleana en el
> modelo de un punto), footprint `[propext, Quot.sound]`. **El mismo enunciado que
> `derives0_consistent`, sin `Classical.choice`.** Ver §5.12.
>
> ⬜ **Lo que queda no es matemática sino firma**: el muro `String`, §7.
>
> 🏁 **Y sobre las dos vías cerradas se ha ido construyendo un CATÁLOGO de metateoremas**, §6.5–§**6.11**: compacidad y LS descendente (054), consistencia finitaria (053), Herbrand de bloque (055), Skolem/Henkin conservativo (056), la capa prenexa (057), la forma normal prenexa (058), Skolem con término (059), bajo un prefijo `∀ⁿ` (060) y 🏁 **la FORMA NORMAL de Skolem** (062).
> ⚠️ Lo excluido del catálogo va con su razón **medida** en ADR‑054 §4 (propiedad de subfórmula, conservatividad de los 107 `codingAxioms`, Church): **falsos o no enunciables**, no «pendientes».
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
| **H3** | **normalización / eliminación de cortes de `Derives₀`** | **era la pieza grande.** Se hizo por la ruta estándar: secuentes `LK₀` sin corte, `LK₀ → Derives₀` por la semántica y `Derives₂ → LK₀+corte` (`ndToLK`), y el corte eliminado allí | 🏁🏁🏁 **HECHA** 2026‑09‑17 — `hauptsatz`, §5.11 |
| **H4** | **extracción de testigos** de una prueba sin cortes | mecánico una vez está H3 | 🏁 **HECHO** (⟸ el 09‑16, ⟹ con H3) |

🏁🏁🏁 **LOS CUATRO HITOS, CERRADOS.** El teorema de Herbrand para `Derives₀` es un
**bicondicional sin hipótesis** (`FOL.Hauptsatz0.herbrand`), footprint `[propext, Quot.sound]`:
**ni un `Classical.choice`, ni un axioma del proyecto**. ⇒ **la vía H está entera** — §5.11.

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

🏁 **Y H3 ya está** (§5.11, 2026‑09‑17). H1+H2 siguen siendo la base y no el teorema, pero el
teorema está encima.

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

🏁 **Y la comprobación de que `LK₀` no es demasiado fuerte, HECHA** (ADR‑048,
`../FOL/FOL/SequentSound0.lean`, 173 l.):

    lkc_sound       : LKc Γ Δ → ∀ M v, (todo Γ vale) → algún elemento de Δ vale
    lk0_to_derives0 : LK₀ Γ Δ → Γ ⊢₀ disjOf Δ
    lk0_not_empty   : ¬ LK₀ [] []

⭐ **Y salió mucho más barata de lo estimado, por la ruta SEMÁNTICA.** Aquí decía:

> ⚠️ **Y una comprobación que NO está hecha**: `LK₀ Γ Δ → Derives₂ Γ (disjOf Δ)` … ⬜ El obstáculo
> está identificado: el caso `allR` exige sacar una disyunción de dentro de un cuantificador
> (`∀x(A ∨ C) → (∀x A) ∨ C` con `C` sin `x`).

Ese obstáculo es real **por la vía sintáctica**. Por la semántica el caso `allR` es rutina, y el
resultado sintáctico cae **como corolario** vía `completeness₀` (§6) y `derives0_iff_derives2`.
🔑 *Cuando las dos direcciones están demostradas, un resultado sintáctico se puede comprar por la
semántica* — primera vez que este plan cobra ese dividendo, y sólo se puede desde ADR‑041.

⭐⭐ **Y el caso `cut` es semánticamente TRIVIAL** (tres líneas). 🔑 *El corte es gratis para la
verdad y carísimo para la demostración*: eso es, en una frase, todo el frente H3.

---

### 5.8 · 🏁 H3, cuarta pieza: **`NDtoLK` demostrada** — queda UNA deuda (ADR‑049)

    ndToLK : Derives₂ Γ f → LKc Γ [f]
    herbrandExtraction_of_cutElim : CutElim → HerbrandExtraction

`../FOL/FOL/NDtoLK0.lean`, **118 l. de código**, `[propext, Quot.sound]` — **ni un
`Classical.choice`**; `mpLK` y `viaEqImpl` **sin ningún axioma**.

⇒ 🏁 **De las dos obligaciones de §5.7 queda UNA: el Hauptsatz.**

#### ⭐⭐ Lo que desbloqueó la traducción: una REGLA, no más esfuerzo

§5.7 midió el bloqueo y lo midió bien: con las instancias de igualdad **en el antecedente**, el
caso `intro_forall` **levanta el contexto**, la `E` de la hipótesis de inducción vive arriba, y una
instancia con `Term.var 0` **no es el levantamiento de ninguna**.

⭐ La salida no fue pelear el bookkeeping sino **añadir la regla que faltaba** — `eqAx`, el **corte
contra un axioma de la teoría**:

| | antes | ahora |
|---|---|---|
| `NDtoLK` | ⛔ bloqueada | ✅ **demostrada**, traducción **estructural** y sin `E` |
| `lk0_herbrand` | devolvía `ts` | ⭐ devuelve `ts` **y** la `E` que la derivación usa |
| `CutElim` | estándar | estándar: los axiomas son **sin cuantificadores** y permutan como cualquier regla izquierda |

🔑 *Cuando una obligación se bloquea por bookkeeping, a veces lo que falta no es esfuerzo sino una
regla.*

⚠️ **Y el diseño está FORZADO, no elegido**: `eqAx` no puede ser una regla **derecha** de igualdad
(`⟹ t ≐ t`), porque `peval` trata `t ≐ t` como un **átomo** y bajo una valuación arbitraria es
falso. El certificado sólo puede decir *«la disyunción se sigue de `E`»*, así que la `E` tiene que
existir. **La forma de `HerbrandCert` fija la forma del cálculo.**

⭐ Y dos cosas salieron **directas, sin corte**: `intro_forall` es literalmente `allR`, y `elim_ex`
es `exL`. *Los dos cálculos tienen la misma regla de eigenvariable, escrita de dos maneras.*
⚠️ El caso con más trabajo fue `forall_not_ex_not`, que cierra otra vez con
`substFormula_lift_var` — el lema del paso de eigenvariable de Henkin, **por tercera vez**.

#### ⬜ Lo que queda de toda la vía H: **una línea**

    CutElim : ∀ Γ Δ, LKc Γ Δ → LK₀ Γ Δ

---

### 5.9 · 🔶 H3, quinta pieza: el ANDAMIAJE del Hauptsatz — 2026‑09‑17, ADR‑050

⛔ **El Hauptsatz NO está.** Esto es lo que hay que tener **antes** de intentarlo, construido y
verificado por partes (`../FOL/FOL/Hauptsatz0.lean`, **218 l. de código**):

    CutAdm               -- el corte ÚNICO, que es lo que un Hauptsatz demuestra
    cutElim_of           -- ⭐ CutAdm ⇒ CutElim, DEMOSTRADO (quince líneas)
    LKh                  -- el cálculo INDEXADO POR ALTURA (14 ctors)
    lkh_mono · lkh_to_lk0 · lk0_to_lkh
    liftFormula_subst_le -- ⭐ la conmutación De Bruijn que FALTABA en el repo

⇒ **H3 se enuncia ahora sobre el CORTE ÚNICO**, que es el objeto sobre el que la literatura razona.

⚠️⚠️ **Por qué hace falta indexar por altura**: la prueba de Gentzen es una **inducción doble**
—grado de la fórmula de corte × suma de alturas—, y ⛔ **la altura no se puede definir sobre
`LK₀`**: vive en `Prop`, no hay eliminación grande, no existe `altura : LK₀ Γ Δ → Nat`.

⭐ Y `LKh.struct` se declara **preservando la altura**: eso da debilitamiento, contracción e
intercambio **gratis dentro de la inducción**, que es justo lo que en la presentación clásica
obliga a pasar por la regla **MIX** en vez del corte. *Una decisión de diseño del inductivo se come
una complicación entera de la prueba clásica.*

#### ⛔ Dos conmutaciones De Bruijn que el repo NO tenía — medido, no estimado

| lema | condición | dónde |
|---|---|---|
| `substFormula_lift_comm` | `k = v` | `Theorems/Eq.lean` |
| `liftFormula_subst` | `v ≤ k` | `Lift0.lean` |
| ⭐ `liftFormula_subst_le` | **`k ≤ v`** | **hecho aquí** |
| ⬜ Barendregt general | `substFormula v s (substFormula 0 u f) = …` | **falta** — `subst_subst_comm_succ` sólo cubre índices **adyacentes** |

#### 🏁 Lo que faltaba para `CutAdm` — **dos de tres, HECHAS** (§5.10)

1. 🏁 la segunda conmutación (**Barendregt general**), ~90 l. estimadas → **99 l.**, riesgo bajo
   confirmado — hecha el 2026‑09‑17, §5.10;
2. 🏁 **`lkh_subst`** (el cálculo cerrado por sustitución, preservando altura), ~150 l.
   estimadas → **133 l.** — hecha el 2026‑09‑17, §5.10;
3. ⬜ **la inducción doble**, ~400–600 l., **riesgo alto**. Es la pieza grande, y ya la única.

⚠️ **Y no hay atajo semántico, que conviene dejar escrito**: `CutAdm` **no** sale de `lkc_sound`
+ `completeness₀`, porque `completeness₀` devuelve una derivación de **`Derives₀`**, no de `LK₀`, y
convertirla exigiría `Derives₀ → LK₀` **sin corte** — que *es* el Hauptsatz. **El círculo se
cierra.**

---

### 5.10 · 🏁 H3, sexta pieza: las DOS conmutaciones y `lkh_subst` — 2026‑09‑17, ADR‑051

⛔ **El Hauptsatz sigue sin estar.** Pero de las **tres** piezas que §5.9 dejaba abiertas, **dos
están hechas** y queda **una sola**, que es la grande. `../FOL/FOL/Hauptsatz0.lean`, §5 y §6:

    §5  substTerm_subst_le · substTerms_subst_le · substFormula_subst_le    --  99 l.
    §6  eqInstance_subst · map_lift_subst · map_sub · lkh_subst             -- 133 l.

#### ⭐ (1) Barendregt, en su forma GENERAL — y por qué generalizar ABARATÓ

    substFormula v s (substFormula w u f)
      = substFormula w (substTerm v s u) (substFormula (v+1) (liftTerm w s) f)     -- con `w ≤ v`

⚠️ El enunciado que §5.9 estimaba era el caso **`w = 0`**, que es el único que `lkh_subst` usa.
**Hubo que generalizarlo a `w` arbitrario** para que la recursión bajo el binder (`w+1 ≤ v+1`) se
cerrara sobre sí misma. 🔑 *Y salió más barato así* — es el quinto corolario de «medir la forma»:
**generalizar puede abaratar**, porque los pasos caros suelen ser artefactos de la instancia.

El caso que paga es `.var n` con `n = v+1`, donde hay que **deshacer** un levantamiento:
`(substTerm_liftTerm s w (substTerm v s u)).symm`. Los otros seis salen por tricotomía y `omega`.

#### ⭐⭐ (2) `lkh_subst` — cerrado por sustitución, **preservando la altura**

    lkh_subst : LKh n Γ Δ → ∀ v t, LKh n (Γ.map (substFormula v t)) (Δ.map (substFormula v t))

**La altura es la misma `n`** — que es justo lo que la inducción doble necesitará: *sustituir no
puede encarecer la derivación*. Catorce casos, y sólo cuatro son trabajo:

| casos | qué hacen | qué paga |
|---|---|---|
| `allR`, `exL` | **cambian el entorno** (bajo el binder: `v+1`, `liftTerm 0 t`) | `liftFormula_subst_le` (§5.9), vía `map_lift_subst` |
| `allL`, `exR` | **instancian** (el testigo viaja a `substTerm v t s`) | **Barendregt general** (arriba) |
| `eqAx` | nada: `eqInstance_subst`, cinco casos, **sin ningún axioma** | — |
| los otros nueve | `simp only [List.map_cons, substFormula]` | — |

⭐ Y aquí se cobra la decisión de diseño de §5.9: **`struct` preserva la altura**, luego
debilitamiento, contracción e intercambio son **un caso más** y no una complicación aparte.

#### 📏 Footprint

`eqInstance_subst` **sin ningún axioma**; `substFormula_subst_le` y `lkh_subst`,
`[propext, Quot.sound]`. **Ni un `Classical.choice`** en todo el módulo.

#### 🏁 Lo que quedaba: UNA pieza — **HECHA** (§5.11)

🏁 La inducción sobre el grado, estimada en ~400–600 l. y **riesgo alto** → **medido 605 l.**
⭐ Y la inducción **doble** (grado × suma de alturas) **no hizo falta**: ver §5.11.

---

### 5.11 · 🏁🏁🏁 **H3 CERRADA: EL HAUPTSATZ** — 2026‑09‑17, ADR‑052

`../FOL/FOL/Hauptsatz0.lean` §7‑§8, **605 l. de código nuevas** (1 023 en total):

    hauptsatz           : CutAdm               -- ⭐⭐⭐ el corte es ADMISIBLE en LK₀
    cut_elimination     : CutElim
    herbrand_extraction : HerbrandExtraction   -- H3, que era LA deuda
    herbrand            : ([] ⊢₀ ∃φ) ↔ ∃ ts E, HerbrandCert φ ts E   -- ⭐ ya INCONDICIONAL

📏 `[propext, Quot.sound]` en todo. **Ni un `Classical.choice`, ni un axioma del proyecto.**

⇒ **La vía H está entera**: H1+H2 (§5.4, Kalmár, net‑0), H3 (aquí) y H4 (§5.4, el certificado).
El teorema de Herbrand para `Derives₀` es un **bicondicional sin hipótesis**, y su mitad `←` se
verifica **por cómputo** (`ptautCheck` reduce ⇒ `by rfl`).

#### ⛔⛔ La corrección que §5.9 dejó anotada, y era

§5.9 declaró `LKh.struct` **preservando** la altura y escribió: *«si la inducción doble no cierra,
el primer sospechoso es `struct`»*. **Lo era**: con la altura preservada el caso `struct` recurre
sobre una premisa de la **misma** altura ⇒ la medida no decrece. Costó **tres ediciones**, y
`lkh_subst` no se movió.

⭐ **Y no se perdió el dividendo**: lo que evita la regla **MIX** de Gentzen no es la altura de
`struct`, es que el enunciado del corte pida **PERTENENCIA** (`Or (x = A) (x ∈ Δ)`) en vez de la
forma `A :: Δ`. 🔑 *Lo que mata a MIX es el ENUNCIADO, no el constructor.*

#### ⭐⭐⭐ Y la inducción DOBLE no hizo falta

La prueba clásica cruza las dos últimas reglas: 5 conectivas × 14 casos de la otra derivación.
Aquí son **dos pasadas independientes de 14 casos**, desacopladas por un **dato uniforme**:

    LeftPrin A Γ Δ   -- las premisas de la regla DERECHA principal de A, empaquetadas

| pasada | induce sobre | qué hace |
|---|---|---|
| `cutPrinAux` | la altura `n` de `D2` | analiza `D2` **una sola vez**; los 5 casos principales son las reducciones de grado |
| `cutLeftAux` | la altura `m` de `D1` | analiza `D1`; sus casos principales **delegan** en `cutPrinAux` |

⇒ **`m + n` no aparece en ningún sitio.** 🔑 *Cuando dos análisis de casos se cruzan, lo que los
desacopla es encontrar el DATO que uno le pasa al otro* — el mismo patrón que `eqAx` en §5.8: **el
desbloqueo no fue esfuerzo, fue una definición.**

⛔ Y `LeftPrin` es **`False`** para `⊥`, átomos e igualdades —no hay regla derecha que las
introduzca—, lo que **cierra gratis** el caso `botL` con `A = ⊥`.

#### ⭐ `lkh_lift`, la otra clausura

Permutar el corte a través de un `allR`/`exL` del otro lado obliga a **levantar la derivación
entera y la fórmula de corte** ⇒ `lkh_lift`, gemela de `lkh_subst` y también **preservando
altura**. ⭐ Sus tres lemas ya existían y **el catálogo los decía**, porque `Theorems/Eq.lean` y
`Lift0.lean` se proyectaron en §5.10/ADR‑051. *Antes de construir, buscar* — esta vez salió bien.

⚠️ Y el índice tiene que ser **general** (`k` arbitrario): el caso `allR` recurre con `k+1`. Misma
lección que el Barendregt de §5.10 — **generalizar es lo que cierra**.

#### ⚠️ Lo que esto NO dice

* **No toca `Derives`**: `hauptsatz` es sobre `LK₀`; el puente a la deducción natural es `ndToLK`
  sobre `Derives₂`. **M‑11 y ADR‑032, intactos.**
* **No dice nada sobre `axioms ⊢`**: ese cálculo es sintácticamente completo (ADR‑024).
* El atajo semántico **seguía sin existir**, como §5.9 dejó escrito. Se pagó sintácticamente.

---

### 5.12 · 🏁 EL DIVIDENDO: la consistencia de `Derives₀` **sin `Classical.choice`** — ADR‑053

`../FOL/FOL/Finitary0.lean`. **El mismo enunciado, footprint estrictamente menor:**

| teorema | ruta | footprint |
|---|---|---|
| `derives0_consistent` (§4, ADR‑034) | semántica: `derives0_soundness` + el modelo `Mtrue` | `[propext, **Classical.choice**, Quot.sound]` |
| ⭐⭐ `derives0_consistent_fin` | **sintáctica**: `ndToLK` + `cut_elimination` + `lk0_tval` | **`[propext, Quot.sound]`** |

🔑 Es el mismo patrón que `derives0_em`/`derives0_peirce` (§5.4), demostrados dos veces —por
completitud y por Kalmár— con footprint estrictamente menor por la vía H.
*Mismo enunciado, menos supuestos.* Y es lo que un plan finitista debería querer por encima de todo.

#### ⚠️ De dónde venía el `Classical.choice`, MEDIDO — y NO era del modelo

`derives0_consistent` **ya** usaba un modelo de un punto (`Mtrue : Model Unit`,
`../FOL/FOL/Soundness0.lean`). El coste venía de `derives0_soundness`, cuya prueba usa **cuatro
`Classical.byContradiction`** (`Soundness0.lean:172‑182): `eval` devuelve `Prop` y la semántica de
Tarski es clásica. 🔑 *El modelo era finitario; la SOLIDEZ no.*

#### ⭐ La salida: evaluar a `Bool`, no a `Prop`

`tval a : Formula → Bool` — el modelo de un punto **calculado**: `⊥ ↦ false`, igualdades `↦ true`,
átomos `↦ a`, y los cuantificadores **desaparecen** (dominio de un elemento). Entonces el caso
`implR` —«o vale `A ⇒ B`, o vale algo de `Δ`»— se resuelve con `cases h : tval a A`, análisis de
casos sobre un `Bool`. **La misma disyunción, sobre `Prop`, exige `em`.**
🔑 *La no‑constructividad no estaba en la matemática: estaba en el TIPO DE LLEGADA del evaluador.*

⭐ Y `tval_eqInstance` **no depende de ningún axioma**: los cinco axiomas de la igualdad son `eq`‑ o
`impl`‑shaped ⇒ la regla `eqAx` (el theory‑cut de §5.8) **no cuesta nada aquí**.

#### ⛔⛔ RECTIFICADO: el Hauptsatz NO hacía falta

⚠️ La primera versión de esta sección decía que el Hauptsatz pagaba en el paso `LKc → LK₀`.
**Falso como afirmación de necesidad**, y lo destapó una medición externa: el caso `cut` de la
solidez booleana son **cinco líneas** —*el corte es gratis para la verdad*—, luego la inducción se
hace directamente sobre `LKc` (15 casos) y se para ahí:

    Derives₀ [] ⊥  →  Derives₂ [] ⊥  →  LKc [] [⊥]  →  False
                (derives0_iff_derives2)  (ndToLK)   (lkc_tval)

⇒ `FOL/Finitary0.lean` **no importa `FOL.Hauptsatz0`**, y ése es el control.
🔑 *Un dividendo atribuido a la pieza equivocada sobrevive hasta que alguien mide* — segunda vez en
dos días (§5.11 §1 ya corrigió lo de `struct`). ⇒ esto **estaba disponible desde ADR‑049**.
El Hauptsatz vale por **Herbrand**, no por esto.

#### ⭐⭐ Y lo que sí mejora, que es más de lo que parecía

`lk0_not_empty` (`../FOL/FOL/SequentSound0.lean:300`) demuestra hoy `¬ LK₀ [] []` **pasando por
`completeness₀`** ⇒ **la consistencia del cálculo de secuentes se compra con la completitud**, y
arrastra el `Classical.choice` que §6.3 identifica como el **WKL**. `lk0_empty`/`lkc_empty` lo
sustituyen net‑0, y son **más fuertes**.

⬜ **Lo que NO se retira**: `derives0_consistent` se queda. Documenta la otra ruta y su precio.

---

### 5.13 · 🔶 Herbrand para un BLOQUE de existenciales — 2026‑09‑17, ADR‑055

⚠️ §5.1 promete el titular **con barras de tupla**: `⊢₀ ∃x̄ φ(x̄) ⟺ ∃ t̄₁…t̄ₙ : ⊢ᵖʳᵒᵖ …`.
Lo que §5.11 entregó es el caso **n = 1**. Aquí van las tuplas — la mitad que se puede pagar hoy:

    derives0_exBlock_of_cert : HerbrandCertBlock n φ tss E → [] ⊢₀ exBlock n φ   -- ⟸ PAGADA
    HerbrandExtractionBlock  : Prop                                              -- ⟹ ENUNCIADA
    herbrand_block_iff       : la deuda con su CONSUMIDOR delante

`../FOL/FOL/HerbrandBlock0.lean`, 120 l. 📏 `[propext, Quot.sound]`, ni un `Classical.choice`.
⭐ Y la ⟸ es **incondicional y sin el Hauptsatz**: `intro_ex` n veces bajo `elim_or`.

⭐ **La pieza de riesgo y su lección**: todo cuelga de `subst_exBlock`, y el índice va `n + k` y no
`k + n` **a propósito** — con `k + n`, el caso `k = 0` obliga a reescribir con `Nat.zero_add` en
cada uso, porque `0 + n` no es `n` por definición. 🔑 *El orden de una suma en un enunciado no es
cosmético: decide si el consumidor reescribe o no.*

⬜ **La mitad ⟹ NO sale por composición** —el cuerpo de un bloque de altura ≥ 2 no es sin
cuantificadores, luego `herbrand` no aplica—: hay que **rehacer la inducción de 14 casos de
`lk0_herbrand` con un invariante más rico**. ⭐ Está comprobado que el invariante **se cierra**
(`exR` baja de `exBlock (m+1) ψ` a `exBlock m ψ'` con `ψ'` sin cuantificadores), pero hay que
llevar la tupla parcial y la salida pasa a `List (List Term)`. **~350–450 l., riesgo alto** — no
las ~250 estimadas.

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

### 6.5 · 🏁 COMPACIDAD y LÖWENHEIM–SKOLEM DESCENDENTE — 2026‑09‑17, ADR‑054

`../FOL/FOL/Compacity0.lean`, 60 l. de código:

    compactness₀           : IsSatisfiable S ↔ (todo subconjunto FINITO de S es satisfacible)
    loewenheim_skolem_down : IsSatisfiable S → IsSatisfiableCountable S

📏 `[propext, Classical.choice, Quot.sound]` — el `Classical.choice` es el **WKL** de §6.3, vía
`completeness₀`. **No se añade fuerza nueva.** ⛔ Es vía W, no vía H: **no es finitario**.

⭐ **Repara** el `compactness_theorem` que `cuarentena/README.md:90` declara **VACUO** («su prueba
pasaba por `soundness`»). Mismo teorema, **sujeto** cambiado. De los tres módulos apartados, el
único cuyo defecto queda reparado fuera.

⭐⭐ Y la mitad difícil no hubo que demostrarla: `DerivesSet₀` (`Henkin0.lean:82`) pide un contexto
**finito por construcción** ⇒ *la compacidad sintáctica estaba metida en la definición*.

⭐ LS descendente: la obstrucción era el **enunciado**, no la prueba — sin Mathlib no hay
`Countable`, y hubo que escribir `CountableDom D := ∃ e : Nat → D, ∀ d, ∃ n, e n = d`.
🔑 *El modelo que la completitud construye ya era numerable; faltaba poder decirlo.*
⚠️ Con un coste que el enunciado obliga: `IsSatisfiable` esconde el dominio bajo un `∃`, luego la
numerabilidad **no se añade a posteriori** — hay que rehacer `model_existence_lemma₀` con ella
dentro. *Un `∃` que oculta un dato impide añadirle propiedades después.*

---

### 6.6 · 🏁 El axioma de SKOLEM/HENKIN es CONSERVATIVO — 2026‑09‑17, ADR‑056

`../FOL/FOL/Skolem0.lean`, 110 l.:

    evalFormula_updateFunc : ¬ occursFormula c f → (eval (updateFunc M c F) v f ↔ eval M v f)
    henkin_conservative    : c fresco para Γ, A, φ → (henkinAx c A :: Γ) ⊢₀ φ → Γ ⊢₀ φ

⭐⭐ **El bloqueo medido eran 70 líneas, y son net‑0.** No había **ningún** lema que conectara
`occursFormula` (sintáctico) con `evalFormula` (semántico): sin él, la frescura de un símbolo no
decía nada semánticamente. `evalFormula_updateFunc` **no depende de ningún axioma** y es
reutilizable por cualquier argumento de frescura.

⭐ **Y el axioma de Skolem ya estaba escrito**: `henkinAx` (`Henkin0.lean:90`). *Antes de construir,
buscar* — van siete. ⚠️ Lo que había sobre él era `henkin_step_consistent` (§6.2): que preserva la
**consistencia**. La conservatividad es **estrictamente más fuerte**.

⚠️ La frescura se usa **tres veces** y cada una hace algo distinto: en Γ transporta el contexto, en
A elige el testigo (y en la rama sin testigo hace que el axioma valga **vacuamente**), y en φ trae
la conclusión de vuelta. *Una hipótesis de frescura usada tres veces no es una.*

⬜ **No incluye**: la capa prenexa sobre `Derives₀` (port de `Theorems/Quantifiers.lean`, ~250–350
l., riesgo bajo) ni la skolemización de fórmulas arbitrarias (falta suministro de símbolos frescos
n‑arios; el de `Fresh0.lean` es de constantes).

---

### 6.7 · 🏁 La CAPA PRENEXA sobre `Derives₀` — 2026‑09‑17, ADR‑057

`../FOL/FOL/Prenex0.lean`, 260 l.: las **ocho** equivalencias de desplazamiento de cuantificador.
📏 Las ocho, `[propext, Quot.sound]`. **Ni un `Classical.choice`.**

⭐ **La condición lateral no se comprueba: se construye.** «x no libre en `B`» es `liftFormula 0 B`
— una fórmula levantada no puede mencionar la variable recién ligada.
🔑 *Una condición lateral codificada en el TIPO no hay que comprobarla.*

⭐⭐ **Y la lógica clásica no entra por Lean.** Las tres direcciones no intuicionistas salen de
`derives0_em_ctx` (**sin ningún axioma**) y del **constructor** `Derives₀.forall_not_ex_not`.
🔑 *La fuerza clásica de este cálculo está en sus CONSTRUCTORES, no en el metanivel.*

⚠️ **Y corrige una estimación del día anterior**: §6.6 dio la capa prenexa por «un port, riesgo
bajo». **El port era falso** — `Theorems/Quantifiers.lean` tiene seis teoremas y **ninguno** es una
regla de desplazamiento. Las ocho se escribieron desde cero, a ~24 l. cada una (medido con las dos
primeras antes de escribir las seis restantes). 🔑 *«Es un port» es una estimación como cualquier
otra, y hay que medirla.*

⬜ **Falta la forma NORMAL**: `prenex : Formula → Formula` con su terminación y su corrección.
~200 l., riesgo **medio** — lo caro es la **medida de terminación**, no las equivalencias.

---

### 6.8 · 🏁 La FORMA NORMAL prenexa — 2026‑09‑17, ADR‑058

`../FOL/FOL/PrenexNF0.lean`, 240 l.: `prenex : Formula → Formula` y
**`derives0_prenex_iff : (Γ ⊢₀ φ) ↔ (Γ ⊢₀ prenex φ)`**. 📏 `[propext, Quot.sound]`.

⭐⭐ **La terminación no hacía falta.** §6.7 la dio por «lo caro». Las seis fusiones las acepta Lean
por **recursión estructural**: se recurre sobre **un** argumento y se **levanta** el otro, así que
el que cambia no es el de la recursión. 🔑 *Cuando la recursión y la transformación van por
argumentos distintos, no hay nada que medir.*

⚠️ Tercera estimación mía refutada en dos días (§5.11, §6.7 y ésta), y las tres en la misma
dirección: **estimar por la forma del enunciado y no por la del árbol**.

⭐ Las congruencias no se escribieron: `FOL.Derives1` ya las tenía, y **enunciadas en la forma que
hacía falta** (esquemáticas en el contexto). Dos líneas de envoltorio cada una.

🏁 Y **`prenex_isPrenex`**: la salida **está** de verdad en forma prenexa (`[propext]`). La
corrección no lo necesita; **la skolemización sí**. ⚠️ Estimado ~70 l., **medido 95** — la primera
estimación del día que se queda **corta**, por contar «dos inducciones» donde había **seis**
(`mergeX`/`mergeXR` por tres conectivas). 🔑 *Contar las piezas por la DEFINICIÓN, no por la idea.*

---

### 6.9 · 🔶 SKOLEMIZACIÓN: el axioma con término de argumentos fijos — 2026‑09‑17, ADR‑059

`../FOL/FOL/Skolem0.lean`, +45 l.:

    skolem_conservative : c fresco → (skolemAxT c t̄ A :: Γ) ⊢₀ φ → Γ ⊢₀ φ

⛔ **Un bloqueo que yo declaré y no existe.** §6.6 dijo que faltaba «suministro de símbolos frescos
**n‑arios**». Medido: `Term.func` toma una lista de **cualquier** longitud —la aridad **no está en
el tipo**— y `occursFormula` mira el **nombre**. `cst : Nat → String` ya los da todos.
⚠️ **Cuatro** obstrucciones mías refutadas en dos días. 🔑 *Declarar un bloqueo es una MEDICIÓN.*

⭐ **Y `t̄` no necesita ser fresco**: con argumentos fijos la interpretación del símbolo nuevo puede
ser **constante**, y entonces no hace falta relacionar la lista de argumentos con el entorno De
Bruijn. *Cuando la interpretación que se construye es constante, los argumentos dejan de ser un
problema.*

🏁 **El prefijo de universales, PAGADO** — §6.10. La estimación de ~200 l. se quedó en **113**,
y el ahorro vino de una sola elección de definición.

---

### 6.10 · 🏁 SKOLEM bajo un PREFIJO `∀ⁿ` — 2026‑09‑17, ADR‑060

`../FOL/FOL/SkolemN0.lean`, módulo nuevo, **113 l. de código**:

    skolemAxN c n A       := ∀x₀…∀x_{n-1} ( (∃y. A) → A[y := c(x₀,…,x_{n-1})] )
    skolem_conservative_n : c fresco para Γ, A, φ → (skolemAxN c n A :: Γ) ⊢₀ φ → Γ ⊢₀ φ
    skolemAxN c 0 A = skolemAxT c [] A                                        -- por `rfl`

⭐⭐ **El entorno no se RECONSTRUYE, se CONSTRUYE.** `envPush v ds` se define **por `shiftEnv`** y
recurriendo **sólo sobre la lista**, con lo que `envPush v [] = v` y
`shiftEnv (envPush v ds) d = envPush v (d :: ds)` son **`rfl`** ⇒ el paso que atraviesa el binder no
lleva ni un `rw`. 🔑 *Cuando una inducción tiene que atravesar un binder, lo que la abarata es
definir el dato acumulado CON el constructor que el binder va a producir.*

⭐ **Y la fila «no existe nada» de §6.9 era CIERTA — lo que falló fue la conclusión.** `vars` se
escribe con `liftTerms 0` (y no con `List.map (liftTerm 0)`), y con esa forma la conmutación
semántica que hace falta **ya existía** (`eval_liftTerms_ext`, `FOL/Semantics.lean:94`): así
`evalTerms_vars` va de **lista a lista**, sin un solo `funext`. 🔑 *Cuando para el dato que necesitas
no existe nada, elige la DEFINICIÓN del dato de modo que se le aplique lo que sí existe.*

⚠️ **Tres detalles que no son cosméticos**: el contador va `n + ds.length` (no al revés — `Nat.add`
recurre sobre el segundo argumento); la guarda `ds.length = n` es **necesaria**, falsa ya en `n = 1`
sin ella; y `Classical.propDecidable` va **explícito** en `skF`, porque el módulo no abre
`Classical` y el binder de `dite` no tipa con la instancia implícita.

⚠️ **Y la trampa de compilación**: cerrar `evalTerms_vars` con `rw […]` **no vale** — el `rfl`
final de `rw` es `with_reducible`, y ni `evalTerm` ni `shiftEnv` son `@[reducible]`. El `rfl` va a
mano. ⭐ Estaba **predicho** por el refutador del diseño.

🏁 **Y la forma normal, PAGADA** — §6.11.

---

### 6.11 · 🏁 LA FORMA NORMAL DE SKOLEM — 2026‑09‑17, ADR‑062

`../FOL/FOL/SkolemNF0.lean`, módulo nuevo, **350 l. de código**:

    skolemize k f          : ∀ᵐ ψ, con ψ SIN cuantificadores
    skolem_conservative_nf : el BLOQUE ENTERO de axiomas de Skolem no inventa teoremas
    derives0_of_skolemNF   : lo que se demuestra desde la forma normal se demuestra sin ella

⭐⭐ **La recursión se PASA, no se mide.** `skolemize` recurre sobre `substFormula 0 t A`, que no
es subtérmino de `.ex A` ⇒ Lean la compilaría por recursión **bien fundada**, y una definición WF
**no reduce definicionalmente**. Con un **combustible** —que es exactamente `qdepth f`, y sustituir
no lo cambia— la recursión es **estructural** y las tres ecuaciones son **`rfl`**.
⇒ la normalización de una fórmula concreta se comprueba **por cómputo**:

    skolemize 0 (∀∃∀∃ Q(x,y,z,w)) = ∀∀ Q(x₁, c₀(x₁), x₀, c₁(x₀,x₁))       -- `by rfl`
    skolemize 0 (∃y ∀x P(x,y))    = ∀x P(x, c₀)                            -- `by rfl`

🔑 *Cuando una recursión no es estructural, antes de pagar la recursión bien fundada hay que mirar
si el argumento que decrece se puede PASAR, en vez de MEDIR.*

⭐ **La dirección que vale sale NET‑0**: `skolemizeF_impAll` —la forma normal implica el original—
es `intro_ex` bajo el prefijo y no consume **ni un axioma de Skolem**. El `Classical.choice` entra
sólo por `skolem_conservative_n`, que cruza por `completeness₀`: es el **WKL**, y no es nuevo.

⚠️ **Un puente que faltaba**: `occursFormula_lift` **no existía** (había `occursTerm_lift` y
`occursTerms_lift`, y nada para fórmulas). Sin él la frescura no atraviesa `prenex`, y el teorema
final pide una hipótesis que **nadie puede descargar**. *Una conservatividad cuyas hipótesis nadie
puede descargar no es un teorema utilizable.*

⬜ **Lo que NO entrega**: la dirección `φ → skolemize φ` **con** los axiomas (exige empujar el
axioma bajo el prefijo `∀ⁿ`, la regla K iterada — **no medida**), y el **enchufe con Herbrand**:
`skolemNF_shape` da `∀ᵐ ψ` con `QuantFree ψ`, que es la hipótesis exacta de `herbrand`, pero
Herbrand habla de **existenciales** y Skolem los quita ⇒ el ensamblaje real pasa por la negación,
y **no está escrito**.

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

## 7.5 · ⛔⛔ Lo que LÖWENHEIM–SKOLEM ASCENDENTE le exige a la firma — MEDIDO 2026‑09‑17

⚠️⚠️ **Esto cambia el orden de §7.2.** Si LS ascendente entra en la hoja de ruta, la tabla de
candidatos de §7.2 **no sirve como está**, y la razón es de una línea:

> `List Char` es **numerable**. `Nat` es **numerable**. Y el requisito que §7.2 escribe —
> «**infinito numerable**», línea 1007 — es **incompatible** con LS ascendente para κ arbitrario.

MEDIDO, y esto no es una limitación pendiente de comprobar: `natToTerm_surj`
(`../FOL/FOL/Enumeration.lean:268`) es un **teorema compilado** que refuta que existan κ términos
cerrados distintos para κ no numerable, porque los símbolos son `String` (`../FOL/FOL/FOL.lean:12`).

⇒ **migrar a `List Char` y después querer LS ascendente obliga a migrar DOS VECES.** La firma que
sirve a los dos es un **parámetro** `S` (el tercer candidato de §7.2, el que la tabla marca como el
caro), no un tipo numerable concreto.
🔑 *Una decisión de firma tomada sin mirar al consumidor de más adelante se paga dos veces* — es
«primero el consumidor, después el molde», a escala de repo.

📐 **Tamaño de parametrizar**, medido hoy: **163 módulos / 3 902 declaraciones**
(FOL 42/545 · RPP 121/3 357). Un orden por encima del enhebrado de `AnclaEq` (~440 firmas).

### ⭐ Lo que NO está bloqueado, y suele darse por bloqueado

El **enunciado** de LS ascendente sí es expresable sin Mathlib: `Model D` toma un `Type` arbitrario
(`Semantics.lean:23`) y **`Function.Injective` existe en el núcleo** (medido con `#check`), luego
«modelo de cardinalidad ≥ |I|» se dice. Lo bloqueado es la **ruta de prueba**, no el enunciado.

### ⛔ Y el segundo bloqueo, que es independiente del primero

Toda la maquinaria de Henkin es una **ω‑cadena**: `cst : Nat → String` (`Fresh0.lean:91`),
`LindenbaumStep : Nat → …` (`Lindenbaum0.lean:130`), `hen`/`hidx` (`HenkinLimit0.lean:221`/`:193`).
Para un lenguaje no numerable haría falta **Lindenbaum transfinito** ⇒ **Zorn**, y el compilador
dice que en el núcleo **no existen** `Zorn`, `zorn_le`, `Cardinal`, `Ultrafilter`, `Filter`,
`WellOrderingTheorem`, `Set` ni `Finset`. La vía por ultraproductos tampoco lo esquiva: el lema del
ultrafiltro es Zorn.

⚠️ **Y lo que eso le hace a la narrativa de §6.3**, que hay que decir antes de decidir: hoy el
proyecto publica que la no‑finitud está **localizada en una línea Π⁰₁ que es el WKL**. Zorn es
muchísimo más fuerte. No cambiaría el footprint de Lean —`Classical.choice` ya está—, cambiaría la
**lectura de reversa matemática**, y §6.3 habría que reescribirla. Es la distinción de
«el FOOTPRINT no es CONSTRUCTIVIDAD», aplicada a una decisión futura.

⬜ **Nada de esto decide.** Queda escrito para que se decida con cifras.

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

### 7.4 · 📎 Y va ENGANCHADO a la migración: el encargo de `Sugerencias.md` (2026‑09‑16)

Sanción del propietario: *«lo agregas al cambio de `String` → `List Char` cuando tengamos
realmente el módulo canónico»*. ⇒ **mismo paquete, misma condición**, no un frente aparte.

**La tesis a medir** (⬜ TODO sin etiqueta de medición, y por eso va aquí y no en un ADR):
*M‑10 puede salir del script y entrar en la FIRMA; M‑11 no —es una propiedad del ENTORNO, cuantifica
sobre declaraciones futuras, y ningún juicio de tipos la coge.*

| | qué medir | control adversarial |
|---|---|---|
| ⬜ | ¿bloquea de verdad? Escribir la clase `(verifier · Decidable · adecuado : P Γ f ↔ ∃ c, verifier c ⌜f⌝)`, enunciar Gödel I sobre `[EsREnumerable P]` e intentar instanciarla en `Derives` | ⭐ **que la instancia para `⊢` NO compile, y por qué**. Si compila, la idea está muerta |
| ⬜ | ¿cuánto cuesta `adecuado` para `Prf`? Parece casi gratis porque `Prf` está definido por su verificador — *estimación, y el proyecto ya sabe cómo acaban* | ¿toca el frente `substfc` o no? |
| ⬜ | propagación real **con el compilador**, no por cierre de nombres (el escarmiento: sobreestimó por **dos órdenes**) | ¿cuántas firmas hay que enhebrar, como con `AnclaEq`? |
| ⬜ | ¿hay API de linter usable en v4.31 **sin Mathlib**, y salta al declarar el `axiom`? | ⚠️ punto ciego: un `axiom` en un módulo que no importe el linter **no se mira** ⇒ serían **los dos**, con la misma tabla y **siempre igualdad exacta, nunca cota** |

⚠️ **Por qué va junto y no antes**: las dos cosas tocan **firmas** (`Term.func : String → …` y el
parámetro de clase), y hacerlas por separado obliga a re‑enhebrar dos veces. Es el mismo argumento
de §7.3.

---

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

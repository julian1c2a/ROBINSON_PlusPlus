# PLAN — `NegVerifier`: solidez estructural, decodificador e inversión de los 21 tags

> **Objetivo:** descargar `NegVerifier` y, con ello, la hipótesis `Reflects` de
> `goedel_first_undecidable_omega` — cerrando la **indecidibilidad de `G`** desde la ω‑consistencia
> clásica, sin postulados gödelianos.
>
> **Referencias:** `NEXT-STEPS.md` (bloque 🎯 LO QUE QUEDA, tarea ①) · `PLANNING.md` ·
> `Meta/OmegaReflect.lean` (la reducción, ya hecha) · `GODEL-STATUS.md`
>
> **Autor:** Julián Calderón Almendros · **Creado:** 2026‑07‑13 · **Estado:** SONDEO HECHO (2026‑07‑14)

---

## 🔬 VEREDICTO DEL SONDEO DE SOLIDEZ (2026‑07‑14) — LEER PRIMERO

El sondeo (§0/§8 de este plan) se ejecutó **antes** de escribir código. Dos resultados, uno esperado y
uno **inesperado que reordena el plan**.

### A) SOLIDEZ ✅ CONFIRMADA — el verificador NO acepta pruebas de indemostrables

* **Los 21 tags están TODOS ligados.** 20 vía **⇔** (`lineWF ⟨concl,tag,args⟩ ⇔ concl =eq
  <forma‑estructural>(args)`: la conclusión queda forzada a la forma exacta de los args). El único
  incondicional es **`mp`**, ligado por **`premsOf`**: `premsOf ⟨v1,16,v0⟩ = [implc v0 v1, v0]`, o sea
  la conclusión `v1` sólo vale si `v0⇒v1` y `v0` están demostradas antes. **No queda ningún tag con
  conclusión libre** — que era exactamente el bug de `gen` (`feedback-verifier-soundness`), ya
  arreglado.
* **`thy` sólo inyecta axiomas reales.** `lineWF ⟨v0,15⟩ ⇔ In v0 axiomsCodeT`, y la única vía para
  probar `In · axiomsCodeT` es `ax_inAxC`, que **sólo** da la pertenencia para axiomas **reales**. No
  se puede probar `In basura axiomsCodeT`.
* **Realidad hereditaria.** `formCode` es **estructuralmente rígido e inyectivo** (`formCode φ =
  cons (numeral tag_φ) args`), así que si la conclusión de una línea‑axioma es un `formCode φ` real,
  sus args quedan **forzados** a ser `formCode` reales; y `mp` propaga realidad de la conclusión a las
  premisas. Por inducción, ninguna cadena aceptada produce un `formCode φ` con `⊬φ`.

**⟹ El módulo E (`VerifierSound`) es VIABLE. No hay bug de solidez. NO hay que reforzar esquemas.**

### B) ⛔ HALLAZGO INESPERADO — `axiomsCodeT` es OPACO, y eso BLOQUEA `NegVerifier` (no es insoldez)

`axiomsCodeT := Term.func "axiomsCodeT" []` es un **átomo totalmente opaco**, con **sólo** dirección
positiva (`ax_inAxC` / `prf_inAxC`). **No existe** ninguna forma de **refutar** `In v0 axiomsCodeT`.

**Consecuencia para el plan:** el **módulo D** necesita refutar `chainOk nil t` para cadenas basura.
Una cadena con una línea **`thy` basura** `⟨v0,15⟩` exige, para refutarla, `axioms ⊢ neg (In v0
axiomsCodeT)` — **imposible con `axiomsCodeT` opaco**. Peor: si `formCode φ` (φ indemostrable pero
no‑axioma) aparece **sólo** como conclusión de una línea `thy`, refutar la cadena requiere
`axioms ⊢ neg (In (formCode φ) axiomsCodeT)`, que tampoco se puede. **⟹ `NegVerifier` NO es demostrable
mientras `axiomsCodeT` sea opaco.**

**Esto NO es insoldez.** El verificador es sólido (§A). Es una **limitación de la codificación de la
teoría**: la teoría **no “sabe” que `axiomsCodeT` contiene sólo axiomas** (es la ω‑incompletitud de su
propio predicado de axioma). Es el análogo exacto de que Gödel exige un **predicado de axioma
decidible/refutable**, no meramente r.e.

**Historia:** `axiomsCodeT` **fue concreto** (`=eq listFormCodeM coreAxioms`) y se **retiró en
`7ae7b7b`** por rendimiento (término gigante, problemas de lift), sustituido por el opaco + `ax_inAxC`.
Las piezas siguen: `formCodeM`, `listFormCodeM`, `coreAxioms`, y `axioms` es una **lista finita
concreta** (~35 entradas).

### C) COROLARIO — el fix de `StdChain` que planeé (§1) es FALSO

`cons h t =eq pair h (succ t)` **está en `axioms`** (`ax_L0_cons_def`), y **`nil := zero`**. Luego un
`cons` **es un número** (una pareja de Cantor): **`canon_ne` es FALSO** — un `cons` puede ser
provablemente igual a un numeral. La clase «canónico» NO sirve. La clase correcta es **«con forma de
código»** (cons‑árboles con **cabeza numeral‑tag**), donde la comparación es **rígida y paralela** —
por eso `formCode_ne` funciona y `canon_ne` no. **Pero incluso esa clase no basta hasta resolver (B).**

### ⟹ REORDENAMIENTO DEL PLAN (nuevo camino crítico)

| Paso | Qué | Estado |
|:--|:--|:--|
| **0** | 🔬 Sondeo de solidez | ✅ **HECHO** (este veredicto) |
| **0.5** | **Concretar `axiomsCodeT`** (opción 1: ancla de igualdad, net‑0 axiomas) | ✅ **HECHO** (`cb62c1e`) |
| **1** | Fix `StdChain` = «con forma de código» (NO «canónico»); redefinir el análogo de `canon_ne` | ⏳ |
| A–F | resto del plan (abajo), con la clase de testigos corregida | ⏳ |

**Paso 0.5 — opciones (a decidir con el usuario):**

1. **Recuperar `axiomsCodeT =eq listFormCodeM coreAxioms`** como **teorema/axioma‑ancla** (revertir
   parcialmente `7ae7b7b`). Da la refutación por `formCode_ne` contra cada axioma. Riesgo: el problema
   de rendimiento/lift que motivó su retirada — habría que confinarlo (no expandir el término gigante
   en cada prueba).
2. **Añadir un ancla NEGATIVA** `ax_notInAxC : a ∉ axioms → axioms ⊢ neg (In (formCodeM a) axiomsCodeT)`
   (meta‑axioma dual de `ax_inAxC`). Más barato y confinado, pero **añade un `axiom`** (hay que
   justificarlo: es conservador si `axiomsCodeT` denota exactamente la lista de axiomas).
3. **Reformular `provCodeC'`** para que `thy` referencie los axiomas por **índice acotado** en vez de
   por pertenencia a un código opaco — cambio estructural mayor.

> **Recomendación:** opción **2** (ancla negativa) — es la dual exacta de `ax_inAxC`, que ya existe y ya
> se acepta; mantiene el confinamiento; y su lectura es evidentemente conservadora. **Pero toca las
> anclas de codificación ⟹ requiere sanción explícita del usuario** (regla del proyecto).

---

## 0 · Punto de partida

Ya está hecho (`Meta/OmegaReflect.lean`, HEAD `f53dd4e`):

```lean
theorem reflects_of_omega (hω : OmegaConsistent) (hneg : NegVerifier) (φ) : Reflects φ
theorem goedel_first_undecidable_omega (hcon) (hω) (hneg) : ¬ Prf godelC' ∧ ¬ Prf (neg godelC')
```

Falta **sólo** `NegVerifier`:

```lean
def NegVerifier : Prop :=
  ∀ (φ : Formula), ¬ Prf φ →
    ∀ l : List Term, StdChain l → axioms ⊢ neg (Verifies φ (objList l))
  where Verifies φ t := land (chainOk nil t) (In (formCode φ) (runFn nil t))
```

**Por qué esto NO está bloqueado por Gödel** (a diferencia de la Π₁ universal `⊢ ¬provCodeC' φ`, que
para `φ = ⊥` es `Con(T)`): aquí el testigo es **concreto**, y el chequeo es **finito y estructural**.

---

## 1 · `StdChain` — clase de testigos correcta

> ⚠️ **SUPERSEDIDO POR EL VEREDICTO (§C arriba).** Esta sección proponía «canónico» — **también es
> incorrecto**: `cons h t =eq pair h (succ t)` (`ax_L0_cons_def`) hace que un `cons` **sea un número**,
> luego `canon_ne` es **FALSO**. La clase correcta es **«con forma de código»** (cons‑árboles con
> **cabeza numeral‑tag**), y **el fix queda supeditado al paso 0.5** (`axiomsCodeT`). Lo de abajo se
> conserva como registro del razonamiento (incluida la refutación del «cerrado»).

**Hay un error en la definición actual de `OmegaReflect.lean` que hay que arreglar ANTES de nada.**

Hoy: `IsClosed x := ∀ k, liftTerm k x = x`, y `StdChain l := ∀ x ∈ l, IsClosed x`.

**El problema:** la igualdad de términos **cerrados NO es decidible ni refutable**. Contraejemplo:
`add zero zero` es cerrado y la teoría **demuestra** `add zero zero =eq zero`. Luego «términos cerrados
distintos ⟹ la teoría los refuta» es **FALSO**, y toda la maquinaria de distinción de códigos
(`CodeDistinct`) se cae.

**La clase correcta:** los términos **CANÓNICOS** — los construidos **sólo** con `cons`, `nil`, `zero`,
`succ` (los constructores de código). Sobre ellos:

* la igualdad **sí** es decidible estructuralmente (meta);
* los distintos **sí** son provablemente distintos (`cons_ne_head`, `cons_ne_tail`, `nil_ne_cons`,
  `prf_succ_inj`, `prf_succ_ne_zero`);
* y es **exactamente** el papel que los **NUMERALES** juegan en la ω‑consistencia clásica.

```lean
/-- Términos CANÓNICOS: los del lenguaje de códigos (`cons`/`nil`/`zero`/`succ`). Es el análogo
    de los NUMERALES en la ω-consistencia clásica. -/
inductive IsCanon : Term → Prop
  | zero : IsCanon zero
  | succ {t} : IsCanon t → IsCanon (succ t)
  | nil  : IsCanon nil
  | cons {h t} : IsCanon h → IsCanon t → IsCanon (cons h t)

def StdChain (l : List Term) : Prop := ∀ x ∈ l, IsCanon x
```

**Impacto en la honestidad de la hipótesis:** restringir la clase hace `OmegaConsistent` *más fuerte*
— pero es la **noción clásica** (numerales), no una debilidad. Y sigue siendo **creíble**: si la teoría
es **sólida** y `⊢ ∃A`, entonces `ℕ ⊨ ∃A`, luego hay un testigo real `n`, y su **término canónico** está
en la clase y satisface `A` en `ℕ` — así que `⊢ ¬A[canon n]` contradiría la solidez. ∎

**Tarea 1.0 (bloqueante, ~1h):** cambiar `IsClosed`/`StdChain` por `IsCanon`/`StdChain` en
`Meta/OmegaReflect.lean`. `reflects_of_omega` no cambia (la prueba es agnóstica de la clase).

> 📌 **Lema auxiliar necesario:** `IsCanon t → ∀ k, liftTerm k t = t` (canónico ⟹ cerrado). Trivial por
> inducción. Se usa donde antes se usaba `IsClosed`.

---

## 2 · Arquitectura (6 módulos) y la SINERGIA con D3

```
                    ┌─────────────────────────────────┐
                    │  B · Meta/LineWFCases.lean      │  ← COMPARTIDO con D3 (tarea ② de NEXT-STEPS)
                    │  Los 21 tags: forma + args      │
                    └───────────┬─────────────────────┘
                                │
        ┌───────────────────────┴───────────────────────┐
        ▼ (negativa: NegVerifier)                       ▼ (positiva: hC_dot / D3)
┌───────────────────────┐                    ┌──────────────────────────┐
│ C · Meta/LineWFNeg    │                    │  pcc_lineWF_tracked      │
│ ⊢ ¬lineWF X (X malo)  │                    │  (reflexión punteada)    │
└───────────┬───────────┘                    └──────────────────────────┘
            │
┌───────────▼───────────┐   ┌────────────────────────┐
│ D · Meta/ChainNeg     │   │ A · Meta/CodeDecode    │
│ runFn eval, ¬In, ¬chOk│   │ decodificador          │
└───────────┬───────────┘   └───────────┬────────────┘
            │                            │
            └──────────┬─────────────────┘
                       ▼
            ┌──────────────────────────┐
            │ E · Meta/VerifierSound   │  solidez estructural (objeto ⟹ meta)
            └──────────┬───────────────┘
                       ▼
            ┌──────────────────────────┐
            │ F · Meta/NegVerifierPrf  │  ensamblaje ⇒ NegVerifier
            └──────────────────────────┘
```

> 🔗 **SINERGIA (importante):** el módulo **B** (análisis de los 21 tags) es **el mismo** que necesita
> `hC_dot` (tarea ② de `NEXT-STEPS.md`) para reflejar el átomo `lineWF`. La diferencia es sólo la
> **dirección**: D3 quiere `lineWF X ⇒ Prov(⌜lineWF Ẋ⌝)` (positiva) y `NegVerifier` quiere
> `¬lineWF X ⇒ ⊢ ¬lineWF X` (negativa). **Construir B una sola vez y usarlo para ambas.**

---

## 3 · Lo que YA EXISTE (no rehacer)

| Pieza | Dónde | Qué da |
|:--|:--|:--|
| `Rule` (21 constructores) | `Meta/HilbertSeq.lean:81` | p1 p2 c1 c2 c3 j1 j2 j3 efq q1 q2 q3 eqrefl leibniz p3 ind qconf listInd thy mp gen |
| `stepConcl : List Formula → Rule → Option Formula` | `HilbertSeq:113` | conclusión meta de una regla |
| `checkAux / checkProof` | `HilbertSeq:139` | **verificador META** decidible |
| `Derivation rs φ := ∃ L, checkProof rs = some L ∧ φ ∈ L` | `HilbertSeq:154` | |
| **`derivation_to_prf : Derivation rs φ → Prf φ`** | `HilbertSeq:248` | ✅ **SOLIDEZ META — ya está** |
| `prf_iff_derivation` | `HilbertSeq:397` | `Prf φ ↔ ∃ rs, Derivation rs φ` |
| `lineJustif : List Formula → Rule → Term` | `Representability2:46` | `cons ⟨tag⟩ (cons ⌜A⌝ …)` |
| `lineCode' acc f r = cons (formCode f) (lineJustif acc r)` | `Representability2:72` | una línea = `⟨concl, tag, args…⟩` |
| `proofCode' : List Rule → List Formula → Term` | `Representability2:76` | el **encoder** de cadenas |
| `chainOk_track` / `runFn_track` | `Representability2:145/92` | ✅ dirección **POSITIVA** (meta ⟹ objeto) |
| `formCode_injective` | `Provability:145` | |
| **CodeDistinct** | `Meta/CodeDistinct.lean` | `neg_symm`, `cons_ne_head`, `cons_ne_tail`, `nil_ne_cons`, `charsCode_ne`, `strCode_ne`, `termCode_ne`, `termsCode_ne`, **`formCode_ne`** |
| `ax_lineWF_inv : ∀L. lineWF L ⇒ tagDisj L 20` | `Minimal/Axioms:1171` | la **inversión** |
| `ax_lineWF_cons` | `Minimal/Axioms:1174` | línea bien formada ⟹ es un `cons` |
| 21 × `ax_lineWF_<tag>` (bicondicionales) + 21 × `ax_premsOf_<tag>` | `Minimal/Axioms` | esquemas por tag |
| `lineTag L = nthc L (succ zero)` | `Minimal/Axioms:1163` | |
| `prf_in_cons_iff`, `prf_not_in_nil` | `ChainPrf` | recursión de `In` |
| `prf_runFn_cons`, `prf_runFn_nil`, `prf_carc_cons`, `prf_chainOk_cons/nil` | `ChainPrf`/`ReprPrf` | recursión del verificador |

**Conclusión clave:** la *solidez del verificador META* (`derivation_to_prf`) **ya está**. Lo que falta
es el **puente objeto → meta** (decodificador + acuerdo negativo), no una solidez nueva desde cero.

---

## 4 · MÓDULO A — `Meta/CodeDecode.lean` · el DECODIFICADOR

**Objetivo:** invertir el codificador sobre términos **canónicos**.

```lean
def decodeNat  : Term → Option Nat              -- inverso de `numeral` / `numeralM` (σⁿ0 ↦ n)
def decodeStr  : Term → Option String           -- inverso de `strCode` (vía `charsCode`)
def decodeTerm : Term → Option Term             -- inverso de `termCode`
def decodeTerms: Term → Option (List Term)      -- inverso de `termsCode`
def decodeForm : Term → Option Formula          -- inverso de `formCode`
```

**Round‑trips (los que se usan):**

```lean
theorem decodeNat_numeral  (n) : decodeNat  (numeral n)  = some n
theorem decodeStr_strCode  (s) : decodeStr  (strCode s)  = some s
theorem decodeTerm_termCode(t) : decodeTerm (termCode t) = some t
theorem decodeForm_formCode(φ) : decodeForm (formCode φ) = some φ
```

**Y la dirección crítica (la que hace el trabajo):**

```lean
/-- Si un término canónico decodifica, es EXACTAMENTE el código de lo decodificado. -/
theorem formCode_decodeForm {c : Term} {φ : Formula} (hc : IsCanon c) :
    decodeForm c = some φ → c = formCode φ
```

> ⚠️ **Trampa (numerales):** `formCode` usa `numeral n = σⁿ0`. `decodeNat` cuenta los `succ`. La
> recursión estructural sobre `Term` está bien fundada; **no** intentar `decodeNat` por `Nat`.
>
> ⚠️ **Trampa (`strCode`):** los símbolos van como `charsCode s.toList`. El decodificador debe
> reconstruir la `String` desde los `Char.toNat`. Usar `charToNat_ne` / `charsCode_ne` (ya existen)
> para la inyectividad.

**Luego, el decodificador de reglas y cadenas** (necesita el acumulador para `mp`/`gen`/`thy`, que
referencian líneas anteriores **por índice**):

```lean
def decodeRule  : List Formula → Term → Option Rule          -- inverso de `lineJustif acc`
def decodeLine  : List Formula → Term → Option (Formula × Rule)   -- inverso de `lineCode'`
def decodeChain : Term → Option (List Rule)                  -- inverso de `proofCode'`

theorem decodeChain_proofCode' (rs acc) (h : checkAux rs acc ≠ none) :
    decodeChain (proofCode' rs acc) = some rs        -- round-trip
```

**Estimación:** ~350‑500 líneas. Riesgo: MEDIO (mecánico, pero 21 casos × round‑trip).

---

## 5 · MÓDULO B — `Meta/LineWFCases.lean` · los 21 tags (**COMPARTIDO con D3**)

**Objetivo:** una tabla ejecutable de los 21 tags, usable en **ambas** direcciones.

```lean
/-- Forma estructural de la línea del tag `k`: aridad y ecuación de la conclusión. -/
def tagArity : Nat → Nat                                   -- 0↦2, 1↦3, …, mp↦2, gen↦1, thy↦1
def tagConcl : Nat → List Term → Option Term               -- la expresión estructural en los args
  -- p1 (0):  some (implc a (implc b a))
  -- p2 (1):  some (implc (implc a (implc b c)) (implc (implc a b) (implc a c)))
  -- …
  -- mp/gen/thy: dependen del ACUMULADOR ⇒ ver nota abajo

/-- El bicondicional del tag `k`, uniformizado (envuelve los 21 `prf_lineWF_<tag>`). -/
theorem prf_lineWF_tag (k : Nat) (hk : k ≤ 20) (concl : Term) (args : List Term) :
    Prf (lineWF (cons concl (cons (numeralM k) (objList args))) ⇔ …)
```

> ⚠️ **Trampa (mp/gen/thy):** sus «args» son **índices** (numerales), no códigos, y su `lineWF` depende
> del **contexto acumulado** (`premsOf` no es `nil`). **Tratarlos aparte** de los 18 esquemas
> axiomáticos. Es lo que ya distingue `prf_premsOf_mp` de `prf_premsOf_p1` (= `nil`).

**Uso en las dos direcciones:**

* **D3 (positiva, tarea ② de NEXT-STEPS):** `lineWF X ⇒ Prov(⌜lineWF Ẋ⌝)` — reflejar la ecuación
  estructural con `pcc_eq_tracked` + evaluaciones, y aplicar el bicondicional **codificado**
  (`pcc_thm_inst` de `ax_lineWF_<tag>`).
* **NegVerifier (negativa, este plan):** ver módulo C.

**Estimación:** ~300‑400 líneas. Riesgo: MEDIO. **Es la pieza de mayor apalancamiento del proyecto.**

---

## 6 · MÓDULO C — `Meta/LineWFNeg.lean` · refutación de `lineWF`

**Objetivo:** `lineWFDec X = false → axioms ⊢ neg (lineWF X)` para `X` **canónico**.

```lean
def lineWFDec : List Formula → Term → Bool      -- decisión META de lineWF sobre líneas canónicas

theorem lineWF_neg_of_dec {acc X} (hX : IsCanon X) (h : lineWFDec acc X = false) :
    axioms ⊢ neg (lineWF X)
```

**Árbol de casos (la prueba):**

1. **`X` no es un `cons`** (p.ej. `zero`, `σ0`) ⟹ por **`ax_lineWF_cons`** (`lineWF X ⇒ X =eq cons …`)
   + **`nil_ne_cons`** / distinción `succ`/`cons` ⟹ `⊢ ¬lineWF X`. ✓
2. **`X = cons concl (cons tag args)` pero `decodeNat tag ∉ {0..20}`** ⟹ por **`ax_lineWF_inv`**
   (`lineWF X ⇒ tagDisj X 20`) + refutar los 21 disyuntos con la distinción de numerales
   (`prf_succ_inj` / `prf_succ_ne_zero`) ⟹ `⊢ ¬lineWF X`. ✓
3. **tag = k ∈ {0..20} pero la ECUACIÓN ESTRUCTURAL falla** (`concl ≠ tagConcl k args` como términos
   canónicos) ⟹ por el **bicondicional** `ax_lineWF_<k>` (`lineWF X ⇔ concl =eq expr`) + **`⊢ ¬(concl
   =eq expr)`** (distinción de términos canónicos) ⟹ `⊢ ¬lineWF X`. ✓
4. **tag = k pero la aridad de `args` no cuadra** ⟹ el bicondicional no aplica; refutar por forma
   (`cons_ne_tail` / `nil_ne_cons`). ✓

> 🔑 **LEMA CLAVE que hay que construir** (base de los casos 3 y 4):
>
> ```lean
> /-- Términos canónicos DISTINTOS son provablemente distintos. -/
> theorem canon_ne {a b : Term} (ha : IsCanon a) (hb : IsCanon b) (h : a ≠ b) :
>     axioms ⊢ neg (a =eq b)
> ```
>
> Inducción mutua sobre `IsCanon`, con `cons_ne_head`/`cons_ne_tail`/`nil_ne_cons` (✅ existen) +
> `prf_succ_inj`/`prf_succ_ne_zero` (✅ existen en `NatArithPrf`). **Esto es lo que hace falsa la
> versión con «cerrados» y verdadera la versión con «canónicos».** ~80 líneas.

**Estimación:** ~400‑600 líneas (21 casos). Riesgo: MEDIO‑ALTO (volumen).

---

## 7 · MÓDULO D — `Meta/ChainNeg.lean` · `runFn`, `In` y `chainOk` negativos

```lean
/-- Evaluación META de `runFn` sobre una cadena canónica (la lista de conclusiones). -/
def runFnDec : Term → List Term

/-- La teoría COMPUTA `runFn` en cadenas canónicas. -/
theorem prf_runFn_eval {t} (ht : IsCanon t) :
    axioms ⊢ (runFn nil t =eq objList (runFnDec t))
    -- por recursión: prf_runFn_nil, prf_runFn_cons, prf_carc_cons, prf_concat_*

/-- `In` NEGATIVO: lo que no está en una lista canónica, la teoría lo refuta. -/
theorem prf_not_In_of_notMem {x : Term} {L : List Term}
    (hx : IsCanon x) (hL : ∀ y ∈ L, IsCanon y) (h : x ∉ L) :
    axioms ⊢ neg (In x (objList L))
    -- inducción sobre L: prf_not_in_nil (base) + prf_in_cons_iff + canon_ne (paso)

/-- Decisión META de `chainOk` y su ACUERDO NEGATIVO. -/
def chainOkDec : List Formula → Term → Bool
theorem prf_not_chainOk_of_dec {t} (ht : IsCanon t) (h : chainOkDec [] t = false) :
    axioms ⊢ neg (chainOk nil t)
    -- recursión con prf_chainOk_cons/nil + lineWF_neg_of_dec (módulo C) + premsOf/allIn
```

**Estimación:** ~300‑400 líneas. Riesgo: MEDIO.

---

## 8 · MÓDULO E — `Meta/VerifierSound.lean` · **SOLIDEZ ESTRUCTURAL** (objeto ⟹ meta)

**Éste es el corazón.** Objetivo: si la decisión META acepta la cadena, entonces **es** el código de
una derivación real — y por tanto sus conclusiones son teoremas.

```lean
/-- Una cadena canónica ACEPTADA es el código de una lista de reglas real. -/
theorem chainOkDec_decodes {t} (ht : IsCanon t) (h : chainOkDec [] t = true) :
    ∃ rs : List Rule, ∃ L : List Formula,
      t = proofCode' rs [] ∧ checkProof rs = some L ∧ runFnDec t = L.map formCode

/-- **SOLIDEZ ESTRUCTURAL DEL VERIFICADOR**: cadena aceptada + `⌜φ⌝` entre sus conclusiones ⟹ `Prf φ`. -/
theorem verifier_sound {φ t} (ht : IsCanon t)
    (hok : chainOkDec [] t = true) (hin : formCode φ ∈ runFnDec t) : Prf φ := by
  obtain ⟨rs, L, ht', hchk, hconcl⟩ := chainOkDec_decodes ht hok
  -- de `formCode φ ∈ L.map formCode` y `formCode_injective` sale `φ ∈ L`
  -- luego `Derivation rs φ`, y `derivation_to_prf` cierra   ← ✅ YA EXISTE
  exact derivation_to_prf ⟨L, hchk, by …⟩
```

> ⚠️ **AQUÍ ESTÁ EL RIESGO REAL DEL PLAN.** `chainOkDec_decodes` afirma que el verificador **objeto**
> no acepta **más** de lo que el encoder produce. **Hay que comprobarlo caso por caso**, porque los
> esquemas `ax_lineWF_<tag>` cuantifican sobre **códigos ARBITRARIOS**, no sólo sobre `formCode ψ` de
> fórmulas reales. Ejemplo: `lineWF ⟨implc a (implc b a), 0, a, b⟩` vale para `a`,`b` **cualesquiera**.
>
> **Por qué debería salir (argumento de «realidad hereditaria»):** si la **conclusión** de la línea es
> un `formCode φ` real, la ecuación estructural **fuerza** a que los args sean `formCode` reales,
> porque `formCode` es **estructural e inyectivo** (`implc a b = formCode (A ⇒ B)` ⟺ `a = formCode A`
> ∧ `b = formCode B`). El decodificador (módulo A) es justo lo que formaliza esa implicación.
>
> **PERO OJO — hay que verificarlo para las líneas INTERMEDIAS**, cuyas conclusiones podrían no ser
> `formCode` reales y aun así alimentar un `mp` posterior. **Éste es el punto que puede obligar a
> reformular.** Si apareciera un contraejemplo, significaría que **el verificador objeto es INSÓLIDO**
> (aceptaría cadenas basura que «prueban» `⌜φ⌝` sin `Prf φ`) — lo cual sería un **bug de solidez del
> proyecto entero**, no de este plan, y habría que **reforzar los esquemas** (como ya se hizo con
> `ax_lineWF_gen`, ver `feedback-verifier-soundness`).
>
> 🔬 **ACCIÓN OBLIGATORIA ANTES DE CODIFICAR EL MÓDULO E:** hacer un **sondeo** (≤ 1 sesión) que
> intente construir una cadena canónica basura, aceptada por los axiomas objeto, cuya `runFn` contenga
> un `formCode φ` con `⊬ φ`. Si se encuentra ⇒ **PARAR** y arreglar los esquemas primero.

**Estimación:** ~300‑500 líneas **si el sondeo sale limpio**. Riesgo: **ALTO** (es el único punto que
puede invalidar el plan).

---

## 9 · MÓDULO F — `Meta/NegVerifierPrf.lean` · ensamblaje

```lean
theorem negVerifier : NegVerifier := by
  intro φ hnp l hl
  -- t := objList l  (canónico)
  by_cases hok : chainOkDec [] (objList l) = true
  · -- aceptada: entonces ⌜φ⌝ NO puede estar entre las conclusiones (si estuviera, verifier_sound
    --           daría Prf φ, contra hnp) ⇒ refutar el `In`
    have hnin : formCode φ ∉ runFnDec (objList l) := fun h => hnp (verifier_sound … hok h)
    -- ⊢ ¬ In ⌜φ⌝ (runFn nil t)   [prf_runFn_eval + prf_not_In_of_notMem]
    -- ⇒ ⊢ ¬ (chainOk ∧ In)      [∧-elim derecho + contraposición]
    …
  · -- rechazada: refutar `chainOk`  ⇒ ⊢ ¬ (chainOk ∧ In)
    …
```

**Estimación:** ~100‑150 líneas. Riesgo: BAJO.

Y el cierre:

```lean
theorem goedel_first_undecidable_final (hcon : ConsistentOmega) (hω : OmegaConsistent) :
    (¬ Prf godelC') ∧ (¬ Prf (neg godelC')) :=
  goedel_first_undecidable_omega hcon hω negVerifier
```

**`G` indecidible desde la ω‑consistencia clásica, y nada más.**

---

## 10 · Orden de ejecución, estimaciones y criterios de aceptación

| # | Módulo | Depende de | Líneas | Riesgo | Sesiones |
|:--|:--|:--|--:|:--|--:|
| **1.0** | **FIX** `IsCanon` en `OmegaReflect` | — | ~40 | BAJO | 0.2 |
| **1.1** | **`canon_ne`** (lema clave) | 1.0 | ~80 | BAJO | 0.3 |
| **0** | 🔬 **SONDEO de solidez** (obligatorio) | — | — | **ALTO** | 0.5–1 |
| **A** | `CodeDecode` (decodificador) | 1.1 | 350–500 | MEDIO | 1–1.5 |
| **B** | `LineWFCases` (21 tags) 🔗 *compartido con D3* | — | 300–400 | MEDIO | 1–1.5 |
| **C** | `LineWFNeg` (⊢ ¬lineWF) | B, 1.1 | 400–600 | MEDIO‑ALTO | 1.5–2 |
| **D** | `ChainNeg` (runFn/¬In/¬chainOk) | C, 1.1 | 300–400 | MEDIO | 1–1.5 |
| **E** | `VerifierSound` (**el corazón**) | A, D | 300–500 | **ALTO** | 1.5–2 |
| **F** | `NegVerifierPrf` (ensamblaje) | E | 100–150 | BAJO | 0.5 |

**Total: ~1 900–2 700 líneas · 8–11 sesiones.** Magnitud comparable a **D1** (`repr_pos'`).

**Camino crítico:** `SONDEO → 1.0/1.1 → B → C → D` en paralelo con `A` → `E` → `F`.

### Criterios de aceptación

- [ ] `lake build` verde, **0 sorrys**, 0 warnings.
- [ ] `#print axioms negVerifier` **sin** postulados gödelianos (`d3`, `provFormula_repr`, …).
- [ ] `#print axioms goedel_first_undecidable_final` = `[propext, choice, Quot.sound]` + meta‑reglas ω
      + `ax_induction`/`ax_list_induction` + `ax_inAxC`. **Nada más.**
- [ ] La cadena real (`goedel_first_real'`, `d2_prf`, `goedel_second'`) **intacta**.
- [ ] `repasa_y_proyecta`: cero fantasmas; §41 proyectado al nodo de Incompletitud.

---

## 11 · Trampas conocidas (leer antes de escribir código)

1. **`IsClosed` NO sirve** — usar `IsCanon` (§1). `add zero zero =eq zero` es demostrable.
2. **`mp`/`gen`/`thy` son distintos**: sus args son **índices**, dependen del **acumulador**, y su
   `premsOf` **no es `nil`**. No meterlos en el patrón de los 18 esquemas axiomáticos.
3. **`numeral n = σⁿ0`**: decodificar contando `succ`, con recursión estructural sobre `Term`.
4. **De Bruijn**: `lineWF`/`chainOk` son **átomos cerrados** aquí (los testigos son canónicos), así que
   **no** hay lifting — es el único trozo del proyecto donde eso no muerde. Aprovecharlo.
5. **`lake build` «Replayed»** puede ocultar errores en ediciones sin commitear (ver
   `feedback-build-cache`). Compilar siempre desde RPP, **nunca** `cd FOL && lake build`.
6. **No tocar los axiomas objeto** sin sanción explícita (regla del proyecto). Si el SONDEO obliga a
   reforzar un esquema `lineWF`, **parar y consultar**.

---

**Author**: Julián Calderón Almendros

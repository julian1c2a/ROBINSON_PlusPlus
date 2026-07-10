# Diseño: Predicado de demostrabilidad con **testigo rastreado** (cierre de D3 / Gödel II)

> **Estado:** propuesta de diseño (previa a tocar código). 2026‑07‑05.
> **Autor:** Julián Calderón Almendros (con asistencia).
> **Ámbito:** `ROBINSON_PlusPlus/Meta/*` — capa `Prf` (Hilbert finitario) de Gödel II.
> **Precondición de build:** todo el proyecto compila (67 jobs, 0 sorrys) bajo Lean `v4.31.0`.
> **Documentos hermanos:** [GODEL-D-ARITHMETIZATION.md](GODEL-D-ARITHMETIZATION.md), [GODEL-STATUS.md](GODEL-STATUS.md), [REFERENCE.md](REFERENCE.md) §3.17.

---

## 0 · Resumen ejecutivo

La cadena de Hilbert‑Bernays‑Löb (HBL) sobre `Prf` está completa **salvo D3**:

- **D1** `repr_pos'_prf : Prf φ → Prf (provCodeC' φ)` ✅ (sin postulados).
- **D2** `d2_prf : Prf (provCodeC'(A⇒B) ⇒ (provCodeC' A ⇒ provCodeC' B))` ✅ (sin postulados).
- **D3** reducida por `d3_prf_of_sigma1` a dos lemas de Σ₁‑completitud del verificador:
  - `hC : ∀ p, Prf (chainOk nil p ⇒ provCodeC'(chainOk nil p))`
  - `hI : ∀ x L, Prf (In x L ⇒ provCodeC'(In x L))`

**Diagnóstico (probado en sesión, §2):** `hI`/`hC` son **indemostrables** con la definición actual
de `provCodeC'`, porque el código de la fórmula reflejada **absorbe la variable de lista `#0`**
como `varc 0` (número de Gödel de una variable *libre*), reflejando una fórmula que **no es teorema**.

**Solución (§3–§4):** redefinir la capa de demostrabilidad para que el **código de la fórmula
reflejada rastree el testigo por funciones object** (`tcFn`/`substfc`), exactamente como el lema
diagonal (`diag_arith`) rastrea la sustitución. Esto elimina la absorción: el testigo entra como
**su propio código** (vía `tcFn`), no como una variable libre absorbida.

**Coste:** refactor deliberado, multi‑fase, que **añade** una capa rastreada y **reescribe** `d3`,
sin tocar la solidez de D1/D2/diagonal (que se conservan y se reutilizan como cimientos).

---

## 1 · Contexto: la cadena D1–D3 y el punto exacto de bloqueo

### 1.1 Definiciones vigentes (no cambian su semántica)

```lean
-- ProofChain.lean
def provFormulaC' : Formula :=
  Formula.ex (land (chainOk nil (.var 0)) (In (.var 1) (runFn nil (.var 0))))
noncomputable def provCodeC' (φ : Formula) : Formula := substFormula 0 (formCode φ) provFormulaC'
```

`provCodeC' φ` = «existe una cadena de prueba `p` válida (`chainOk nil p`) cuya lista de
conclusiones (`runFn nil p`) contiene el código `⌜φ⌝`». Es Σ₁.

- `runFn c nil = c`; `runFn c (cons line rest) = runFn (c ++ [carc line]) rest`
  (acumula la conclusión `carc line` de cada línea). — `ReprPrf.prf_runFn_nil/cons`.
- `In x L` = `Formula.atom in_sym [x, L]`; `formCode(In x L) = ⟨3, ⌜∈⌝, [termCode x, termCode L]⟩`.

### 1.2 La reducción `d3_prf_of_sigma1` (ReflectionPrf.lean)

```lean
theorem d3_prf_of_sigma1 (φ)
    (hC : ∀ p, Prf (chainOk nil p ⇒ provCodeC'(chainOk nil p)))
    (hI : ∀ x L, Prf (In x L ⇒ provCodeC'(In x L))) :
    Prf (provCodeC' φ ⇒ provCodeC'(provCodeC' φ))
```

Estructura: `prf_ex_elim_imp` introduce el testigo `p = #0`; en contexto se tienen
`chainOk nil #0` e `In ⌜φ⌝ (runFn nil #0)`; se promueven con `hC`/`hI`; se combinan con
`PrfH_pcc_andIntro` y se `∃`‑introducen con `PrfH_pcc_exIntro (A) (t := #0)`.

### 1.3 Los combinadores internos ya disponibles

```lean
PrfH_pcc_mp       -- D2 interno
PrfH_pcc_prf      -- D1 interno
PrfH_pcc_andIntro -- ∧-intro interno (c1)
PrfH_pcc_exIntro (A) (t) (h : PrfH Γ (provCodeC'(substFormula 0 t A))) : PrfH Γ (provCodeC'(∃A))
```

**El testigo `t` de `PrfH_pcc_exIntro` se sustituye a nivel de la fórmula `A` (`substFormula 0 t A`)
y luego se toma `formCode`.** Ahí nace la absorción (§2).

---

## 2 · Diagnóstico riguroso del muro

### 2.1 Evidencia (sondeo `prf_list_induction`, sesión 2026‑07‑04)

Intentando `hI` por inducción de listas, la meta **base** (tras sustituir `#0 := nil`) es:

```text
⊢ᴴ  substFormula 0 nil ( (In (liftTerm 0 x) #0)  ⇒  provCodeC'(In (liftTerm 0 x) #0) )
```

El consecuente `provCodeC'(In (liftTerm 0 x) #0)` es un **fórmula CERRADO CONSTANTE**:
`formCode(In (liftTerm 0 x) #0)` codifica `#0` como `varc 0 = ⟨0,[0]⟩` (número de Gödel de
una variable *sintáctica*, cerrado). Por tanto **no depende** de la variable de lista `#0` del
esquema de inducción.

### 2.2 Consecuencia

- **Base** (`#0 := nil`): antecedente `In x nil` es **falso** ⇒ la implicación se prueba por explosión.
  (Falso positivo: parece que «va».)
- **Paso** (`#0 := cons hd t`), caso `x =eq hd`: hay que probar **el mismo consecuente constante**
  `provCodeC'(In (liftTerm 0 x) #0)`, que refleja la fórmula `In x' (var 0)` con **variable libre
  `var 0`** ⇒ **no es teorema** ⇒ **imposible**.

### 2.3 Interpretación (Σ₁‑completitud real)

La reflexión Δ₀ correcta exige que el testigo sea un **numeral cerrado** `θ(n̄)` y reflejar la
**instancia cerrada** `⊢ Prov(⌜θ(n̄)⌝)`. Aquí, tras `prf_ex_elim_imp`, el testigo queda
**simbólico** (`#0`) y el código lo trata como **variable libre** (`varc 0`), no como el
**numeral de su valor**. El object‑proof no puede «extraer» el valor numeral del testigo.

**Conclusión.** Ningún lema incremental sobre el `provCodeC'` actual cierra `hI`/`hC`: el defecto
está en **cómo se construye el código de la fórmula reflejada**. Hay que rastrear el testigo con
funciones object (patrón `diag_arith`), no dejar que `formCode` lo absorba.

---

## 3 · Principio de la solución: rastreo del testigo (patrón `diag_arith`)

El lema diagonal ya resuelve un problema idéntico. Recordatorio:

```lean
def diagTerm : Term := substfc (numeral 0) (tcFn (Term.var 0)) (Term.var 0)
theorem diag_arith (ψ) :
  axioms ⊢ (substTerm 0 (formCode ψ) diagTerm =eq formCode (selfApp ψ))
--  prueba: congr_substfc_arg2 (tc_form ψ)  ∘  substFormula_arith 0 (formCode ψ) ψ
```

Claves reutilizables:

- **`tcFn`** (`Minimal/Axioms.lean`, ecuaciones en `axioms`): función **object** que computa
  `termCode` sobre códigos. `prf_tc_form : Prf (tcFn (formCode φ) =eq termCode (formCode φ))`.
  Tiene **congruencia Leibniz object** (`prf_congr_tcFn`), a diferencia de la `termCode` meta.
- **`substfc`** (object) + **`prf_substFormula_arith`**:
  `Prf (substfc (numeral v)(termCode s)(formCode f) =eq formCode (substFormula v s f))`.
- **`provFromCode c := substFormula 0 c provFormulaC'`** + **`prf_provCode_congr`**:
  la demostrabilidad **respeta la igualdad de códigos** (`Prf (c₁=eq c₂) → Prf (provFromCode c₁ ⇒ provFromCode c₂)`).

**Idea central.** El testigo `p` en `d3` es un **código de cadena** (una lista `cons`/`nil` de
códigos de línea). El código que la reflexión debe usar para `p` es **`tcFn p`** (el «código del
código»), no `varc 0`. Con `tcFn`/`substfc` la contribución del testigo al código de la fórmula
reflejada **se rastrea** en vez de absorberse, y la congruencia Leibniz permite transportar la
demostrabilidad.

---

## 4 · Diseño detallado

> Nomenclatura: sufijo **`ₜ`** («tracked») para los objetos rastreados. Los actuales se conservan.

### 4.1 Piezas ya construidas y reutilizables (sesión 2026‑07‑04, en `Sigma1CorePrf.lean`)

| Pieza | Firma | Rol en el nuevo diseño |
|---|---|---|
| `inFormCodeFn xc Lc` | `Term` = `⟨3,⌜∈⌝,[xc,Lc]⟩` | constructor object del código de un átomo `In` |
| `inFormCodeFn_termCode` | `inFormCodeFn (termCode x)(termCode L) = formCode(In x L)` (rfl) | puente meta↔object |
| `prf_congr_inFormCodeFn` | congruencia en `xc`,`Lc` | Leibniz sobre los args |
| `prf_provFromCode_In_congr` | transporte de demostrabilidad por `=eq` de los args | rompe la absorción |
| `prf_provCodeC'_In_of_tracked` | `xc=eq termCode x → Lc=eq termCode L → Prf(provFromCode(inFormCodeFn xc Lc)) → Prf(provCodeC'(In x L))` | puente rastreado → real |
| `objList : List Term → Term` | lista object desde lista meta | testigos concretos |
| `pcc_in_objList_of_mem` | `List.Mem x elems → Prf(provCodeC'(In x (objList elems)))` | reflexión por meta‑pertenencia |
| `prf_runFn_objList` / `prf_runFn_nil_objList` | `runFn nil (objList lines) =eq objList (lines.map carc)` (axiomas puros) | tracking `runFn→objList` |
| `pcc_in_runFn_objList` | `List.Mem x (lines.map carc) → Prf(provCodeC'(In x (runFn nil (objList lines))))` | **`hI` para testigos concretos** |

`prf_congr_tcFn` (en `TcArithPrf.lean`) es la congruencia Leibniz de `tcFn`.

### 4.2 Objetos nuevos a definir

```lean
-- (N1) Código object de la conclusión-membresía RASTREADO por tcFn del testigo.
--      inFormCodeFn ya construye ⟨3,⌜∈⌝,[xc,Lc]⟩; aquí Lc = tcFn del término-lista.

-- (N2) Predicado de demostrabilidad RASTREADO de un átomo In:
def provInTrackedFn (xc Lc : Term) : Formula := provFromCode (inFormCodeFn xc Lc)
--   (xc, Lc = códigos object de los argumentos; NO formCode meta)

-- (N3) Cuerpo Σ₁ RASTREADO del verificador (testigo rastreado por tcFn):
--   provFormulaC'ₜ ≈ ∃p ( chainOkTrackedFn (tcFn #0) ∧ inTrackedFn ⌜φ⌝ (tcFn (runFn nil #0)) )
--   — el código de la conclusión usa tcFn del testigo, no varc 0.
```

> **Decisión de diseño (crítica).** Hay dos formas de introducir el rastreo:
>
> - **Opción A — redefinir el cuerpo Σ₁** (`provFormulaC'ₜ`) para que el slot del código de
>   la conclusión sea `tcFn` del testigo. Es la más limpia semánticamente pero obliga a
>   re‑derivar **D1** para la nueva `provCodeC'ₜ` (necesitación con testigo rastreado).
> - **Opción B — reescribir sólo `d3`** manteniendo `provFormulaC'` y añadiendo un
>   `∃`‑intro rastreado (`PrfH_pcc_exIntro_tracked`) que use `tcFn p` como código‑testigo y
>   `substfc` para el cuerpo. No toca D1/D2, sólo `d3`. **Recomendada como primer intento**
>   por ser aditiva y de menor superficie de rotura.
>
> El resto del documento detalla **Opción B** como ruta principal y marca los puntos donde,
> si B se atasca, se escala a A.

<!-- -->

> **DECISIÓN (2026‑07‑05): Opción A.** Análisis posterior confirma que el `∃`‑intro interno
> (`PrfH_pcc_exIntro`) produce **inherentemente** `formCode(A[0:=testigo])`; para el testigo
> abstracto eso reabsorbe la variable (`varc 0`), y la costura de B (`tcFn p =eq termCode p`) **no
> es enunciable** para `p` abstracto (`termCode p` meta‑stuck). Es una duda que **rompe la prueba
> entera**, no un detalle. Por el criterio «ante duda que pueda traer problemas → A», se adopta
> **Opción A**: rastreo uniforme desde la raíz (`provFormulaC'ₜ`/`provCodeC'ₜ` con `tcFn`/`substfc`)
>
> + re‑derivación de **D1ₜ**. D2 (`pcc_imp`) y el lema diagonal se reutilizan sin cambio estructural.
> Orden de fases A: **A‑F1** ladrillos `tcFn`‑código (computación `tcFn=termCode` sobre las formas
> de lista/cadena) → **A‑F2** `provFormulaC'ₜ`/`provCodeC'ₜ` + puente con `provCodeC'` → **A‑F3**
> `repr_pos'_prfₜ` (D1ₜ) → **A‑F4** `d3_prfₜ` (∃‑intro rastreado nativo) → **A‑F5** `goedel_second_prf`.

### 4.3 Nuevos lemas (firmas objetivo, Opción B)

```lean
-- (L1) ∃-intro interno RASTREADO: el testigo aporta su código tcFn.
--      A = cuerpo con #0 = testigo; el código reflejado sustituye tcFn p (no p como var).
theorem PrfH_pcc_exIntro_tracked {Γ} (A : Formula) (p : Term)
    (h : PrfH Γ (provFromCode (substfc (numeral 0) (tcFn p) (formCode A)))) :
    PrfH Γ (provCodeC' (Formula.ex A))
--   Prueba: substFormula_arith transporta substfc(numeral 0)(termCode(tcFn p))(formCode A)
--           a formCode(A[0 := tcFn p]); congruencia tcFn (prf_congr_tcFn) + prf_provCode_congr
--           reconcilian tcFn p con el código del testigo; luego Q2 interno como en PrfH_pcc_exIntro.
--   RIESGO: requiere que tcFn p = termCode p sea DERIVABLE en el contexto (ver L2).

-- (L2) Puente testigo→código dentro de chainOk: un testigo válido ES un código.
--      chainOk nil p ⇒ (tcFn p =eq termCode p)   -- NO enunciable con termCode meta abstracto.
--      REFORMULACIÓN OBJECT: chainOk nil p ⇒ (tcFn p =eq codeOfChainFn p)
--      donde codeOfChainFn es una función object que recorre p con carc/cdrc.
--      *** Este es el núcleo técnico pendiente. Ver §4.4 y RIESGO‑1. ***

-- (L3) hC rastreado (chainOk): análogo a hI con la estructura cons/nil de la cadena.
theorem hC_tracked (p) : Prf (chainOk nil p ⇒ provCodeC'(chainOk nil p))  -- objetivo final

-- (L4) hI rastreado (In sobre runFn del testigo):
theorem hI_tracked (φ p) :
    Prf (In (formCode φ) (runFn nil p) ⇒ provCodeC'(In (formCode φ) (runFn nil p)))  -- objetivo final
```

### 4.4 El núcleo técnico: rastrear la lista de conclusiones del testigo abstracto

Para `hI_tracked` con `p` abstracto necesitamos reflejar `In ⌜φ⌝ (runFn nil p)`. Estrategia:

1. **Inducción object sobre `p`** (regla `listInd` del verificador, ya integrada:
   `prf_list_induction`), con un predicado **rastreado**:

   ```text
   Ψ(p) := In ⌜φ⌝ (runFn nil p) ⇒ provFromCode (inFormCodeFn (tcFn ⌜φ⌝) (tcFn (runFn nil p)))
   ```

   El consecuente usa **`tcFn (runFn nil p)`**, que **sí depende** de `p` (función object del
   testigo), evitando la absorción.
2. **Base** `p := nil`: `runFn nil nil =eq nil`; `In ⌜φ⌝ nil` es falso ⇒ explosión.
3. **Paso** `p := cons line rest`: `runFn nil (cons line rest) =eq runFn [carc line] rest`.
   Usar `prf_runFn_cons` + IH + los combinadores `pcc_in_head/tail` en su **versión rastreada**
   (código con `tcFn`), transportando por `prf_provFromCode_In_congr`.
4. **Cierre**: convertir `provFromCode(inFormCodeFn (tcFn ⌜φ⌝)(tcFn (runFn nil p)))` en
   `provCodeC'(In ⌜φ⌝ (runFn nil p))` mediante **`prf_provCodeC'_In_of_tracked`**, que exige
   `tcFn (runFn nil p) =eq termCode (runFn nil p)`. **Aquí reaparece el problema**:
   para `p` abstracto, `termCode (runFn nil p)` es meta‑stuck.

   **Resolución de diseño:** no cerrar contra `provCodeC'` (meta) sino **reformular `d3` entero
   sobre `provFromCode`/códigos object** (Opción A parcial dentro de B): `d3` produce
   `provCodeC'(provCodeC' φ)` cuyo bloque interno **también** se expresa con `tcFn`. Es decir, la
   `PrfH_pcc_exIntro_tracked` (L1) consume la versión **rastreada** de `hI`/`hC` (con `tcFn`) sin
   pasar nunca por `termCode` del testigo abstracto. La `formCode` meta sólo aparece para `φ`
   (concreto) y para los símbolos de estructura (concretos), nunca para `runFn nil p`.

> **RIESGO‑1 (el más serio).** Cerrar el paso 4 sin `termCode (runFn nil p)` requiere que **toda**
> la cadena `d3` viva en `provFromCode`/`tcFn` y que `PrfH_pcc_exIntro_tracked` reconcilie el
> código‑testigo `tcFn p` con el `substfc` del cuerpo **sin** una igualdad `tcFn p =eq termCode p`
> global. Es plausible (el lema diagonal lo logra para `ψ` concreto) pero **no verificado** para el
> testigo abstracto. Si se atasca, se escala a **Opción A** (redefinir `provFormulaC'ₜ` con `tcFn`
> desde la raíz y re‑derivar D1ₜ).

### 4.5 `hC` rastreado

`chainOk nil p` es Δ₀ con estructura `cons`/`nil` sobre `p` (validez línea a línea). El patrón es
idéntico a `hI` pero usando los combinadores `pcc_chainOk_nil`/`pcc_chainOk_cons` (ya en
`Sigma1Prf.lean`) en versión rastreada. Depende de las mismas piezas (L1, tracking, `tcFn`).

### 4.6 `d3` rastreado

```lean
theorem d3_prf (φ) : Prf (provCodeC' φ ⇒ provCodeC'(provCodeC' φ)) := by
  -- como d3_prf_of_sigma1 pero:
  --   • ∃-intro con PrfH_pcc_exIntro_tracked (testigo #0 aporta tcFn #0)
  --   • hC/hI reemplazados por hC_tracked/hI_tracked (§4.4–4.5)
  --   • el cuerpo reflejado usa tcFn del testigo en TODOS los slots de testigo
```

Con `d3_prf` cerrado, la cola es mecánica y ya prevista:

- `goedel_second_prf : ConsistentH → ¬ Prf Con'` vía punto fijo (`godelC_fixedpoint` ya existe) +
  necesitación (`repr_pos'_prf`) + D2/D3 en `Prf`.

---

## 5 · Orden de migración (D1 → D2 → diagonal → D3)

**Principio:** cada fase deja el build **verde (0 sorrys)** y se commitea/pushea antes de la siguiente.

| Fase | Contenido | Toca | Verde tras fase |
|---|---|---|---|
| **F0** | Congélese el checkpoint actual (hecho: `3b3a752`). Añadir este doc. | docs | ✅ |
| **F1** | **Combinadores rastreados de `In`/`chainOk`** en versión `tcFn`‑código: `pcc_in_head/tail/nil` y `pcc_chainOk_*` **sobre `provFromCode(inFormCodeFn (tcFn·)(tcFn·))`**. Reusa `prf_provFromCode_In_congr`, `prf_congr_tcFn`, `prf_tc_*`. | `Sigma1CorePrf.lean` (add) | ✅ (aditivo) |
| **F2** | **`PrfH_pcc_exIntro_tracked` (L1)** + `substFormula_arith`/`prf_substFormula_arith` glue. Verificar en un caso concreto (testigo `objList lines`) antes que abstracto. | `Sigma1CorePrf.lean`/nuevo `Sigma1TrackedPrf.lean` | ✅ |
| **F3** | **`hI_tracked` (L4)** por inducción object (`prf_list_induction`) con el predicado rastreado (§4.4). | nuevo módulo | ✅ |
| **F4** | **`hC_tracked` (L3)** análogo (§4.5). | nuevo módulo | ✅ |
| **F5** | **`d3_prf`** ensamblado (§4.6), reemplazando la vía `d3_prf_of_sigma1` (que queda como lema histórico o se retira). | nuevo módulo + `ReflectionPrf` | ✅ |
| **F6** | **`goedel_second_prf`** (punto fijo + necesitación + D2/D3). | nuevo módulo | ✅ |
| **F7** | **Limpieza**: retirar postulados legacy (`Incompleteness.D2/D3`, `GodelTwo.d3`, `diagonal_lemma`) si ya no se citan; `#print axioms goedel_second_prf` debe ser `[propext, choice, Quot.sound]` (+ `prf_inAxC` benigno). | varios | ✅ |

**D1 (`repr_pos'_prf`) y D2 (`d2_prf`) NO se tocan en Opción B.** El lema diagonal (`Diagonal.lean`)
**tampoco**: se reutiliza su maquinaria (`tcFn`/`substfc`/`substFormula_arith`), no se modifica.

> Si en **F2/F3** aparece **RIESGO‑1**, se abre la **rama Opción A**:
> | A‑F1 | `provFormulaC'ₜ` + `provCodeC'ₜ` con `tcFn` desde la raíz. |
> | A‑F2 | **D1ₜ** `repr_pos'_prfₜ` re‑derivada (necesitación con testigo rastreado). |
> | A‑F3 | **D2ₜ** `d2_prfₜ` (probablemente `pcc_imp` se transporta sin cambio). |
> | A‑F4 | reconciliar `provCodeC'` ↔ `provCodeC'ₜ` (equivalencia object) para no rehacer diagonal. |
> Opción A es ~2–3× el esfuerzo de B; sólo se activa si B se demuestra insuficiente.

---

## 6 · Impacto por módulo

| Módulo | Cambio | Riesgo |
|---|---|---|
| `Meta/Sigma1CorePrf.lean` | **add** combinadores rastreados (F1) | bajo |
| `Meta/Sigma1TrackedPrf.lean` (NUEVO) | L1–L4, `d3_prf` | **alto** (núcleo) |
| `Meta/ReflectionPrf.lean` | `d3_prf_of_sigma1` pasa a histórico; export de `d3_prf` | medio |
| `Meta/GodelTwo.lean` | `goedel_second_prf` real; retirar `d3` postulado | medio |
| `Meta/Incompleteness.lean` | retirar D2/D3 postulados legacy (si aislados) | bajo |
| `Meta.lean` (barrel) | imports nuevos | trivial |
| `REFERENCE.md`, `CHANGELOG.md`, `GODEL-STATUS.md` | proyección | trivial |
| **D1/D2/Diagonal** | **sin cambios** (Opción B) | — |

---

## 7 · Riesgos y mitigaciones

1. **RIESGO‑1 — testigo abstracto sin `termCode` (núcleo).** *Mitigación:* verificar L1 y el paso
   inductivo primero para testigos **concretos** (`objList lines`, ya soportado por
   `pcc_in_runFn_objList`) → sube confianza antes del abstracto. Si falla, escalar a Opción A.
2. **De‑Bruijn/normalización bajo binders.** El `substfc`/`tcFn` bajo el `∃` reproducirá los
   patrones De Bruijn ya resueltos (`norm21`/`norm32`/`confinementFormula`). *Mitigación:* reusar
   el toolkit `FOL/Theorems/Eq.lean` y los `norm*` de `ChainPrf`.
3. **Regresión de build (4.31 `simp`).** *Mitigación:* seguir [feedback_fol_toolchain_pitfall]:
   `if_true`/`zero`/`succ` explícitos; inline de contexto donde haya `let Γ`.
4. **`prf_inAxC` en `#print axioms`.** Es un ancla de coding benigna (no gödeliana). *Mitigación:*
   documentar que `goedel_second_prf` cita `[propext, choice, Quot.sound, prf_inAxC]` y por qué es honesto.
5. **Notación scoped `∈`/`=eq`/`≤`.** *Mitigación:* usar `List.Mem` explícito en metanivel (ya en memoria).
6. **Alcance/tiempo.** Es multi‑sesión. *Mitigación:* fases F1–F7 con checkpoint verde y push por fase.

---

## 8 · Criterios de éxito

- [ ] `d3_prf : Prf (provCodeC' φ ⇒ provCodeC'(provCodeC' φ))` sin `sorry` ni postulados gödelianos.
- [ ] `goedel_second_prf : ConsistentH → ¬ Prf Con'` cerrado.
- [ ] `#print axioms goedel_second_prf` = `[propext, Classical.choice, Quot.sound]` (+ `prf_inAxC`).
- [ ] Build completo verde, 0 sorrys, en toda fase.
- [ ] Postulados legacy (`Incompleteness.D2/D3`, `GodelTwo.d3`, `diagonal_lemma`) retirados o
      claramente marcados como no citados por la cadena real.
- [ ] `REFERENCE.md` §3.17 y `GODEL-STATUS.md` proyectados.

---

## 9 · Apéndice — glosario de símbolos citados

| Símbolo | Significado | Ubicación |
|---|---|---|
| `provFormulaC'` / `provCodeC'` | predicado Σ₁ de demostrabilidad estructural | `Meta/ProofChain.lean` |
| `provFromCode c` | `substFormula 0 c provFormulaC'` (demostrabilidad de un CÓDIGO) | `Meta/Sigma1Prf.lean` |
| `formCode φ` | número de Gödel (meta) de la fórmula `φ` | `Meta/Provability.lean` |
| `termCode t` / `termsCode` | código (meta) de un término / lista de términos | `Meta/Provability.lean` |
| `tcFn` | función **object** que computa `termCode` sobre códigos («código del código») | `Minimal/Axioms.lean` + `TcArithPrf` |
| `substfc` | sustitución **object** sobre códigos de fórmula | `Minimal/Axioms.lean` |
| `prf_substFormula_arith` | `substfc(num v)(termCode s)(formCode f) =eq formCode(substFormula v s f)` | `Meta/ArithPrf.lean` |
| `runFn` / `chainOk` / `In` / `carc` | verificador estructural (conclusiones / validez / pertenencia / cabeza) | `Minimal/Axioms.lean` |
| `inFormCodeFn` / `objList` / `pcc_in_runFn_objList` | capa de código object para `In` + tracking `runFn→objList` | `Meta/Sigma1CorePrf.lean` |
| `prf_congr_tcFn` | congruencia Leibniz object de `tcFn` | `Meta/TcArithPrf.lean` |
| `prf_provCode_congr` | demostrabilidad respeta igualdad de códigos | `Meta/Sigma1Prf.lean` |
| `d3_prf_of_sigma1` | reducción de D3 a `hC`/`hI` (a reemplazar) | `Meta/ReflectionPrf.lean` |

---

## 10 · Plan de ejecución de la Opción A DE RAÍZ (D1ₜ) — confirmado 2026‑07‑05b

**RIESGO‑1 se materializó** (verificación concreta en `Meta/Sigma1TrackedPrf.lean`): el ∃‑intro
rastreado (`pcc_exIntro_code`) cierra para testigos **cerrados**, pero para el testigo **abstracto**
`tcFn #0` no es cerrado y —lo decisivo— TODO combinador base (`pcc_in_*`/`pcc_imp`/D1 `repr_pos'`)
emite el código vía **`termCode` meta**; transportar el 2º argumento (la lista abstracta `L`) de
`termCode L` a `tcFn L` está **stuck**. El 1º argumento (elemento `⌜φ⌝`, concreto) sí transporta
(`prf_tc_form`). **Conclusión firme: no hay atajo por D1+transporte.** Se ejecuta **Opción A de raíz**.

### 10.1 Pieza hecha (cimiento)

- `Meta/TrackedCorePrf.lean` — **`liftFormula_provFromCode (k c) (hc : ∀lvl, liftTerm lvl c = c)`**:
  clausura genérica de `provFromCode c` para código cerrado arbitrario (generaliza
  `liftFormula_provCodeC'` y `liftFormula_provFromCode_exc`). La usan D1ₜ y el MP/∃ a nivel código.

### 10.2 D1ₜ — reconstruir la representabilidad emitiendo códigos `tcFn` (el port grande)

Objetivo: **`repr_pos'_prfₜ`** que refleje átomos con el 2º argumento (lista) codificado por `tcFn`
(no `termCode`), de modo que el consecuente **dependa del testigo** y la inducción sobre `p` funcione.

Fuente a portar: `Meta/Representability2Prf.lean` (`proofCode'`, `prf_runFn_track`,
`prf_chainOk_track` 19 casos, `provCodeC'_intro_prf`). Sustituir en la construcción del código de
la prueba la `termCode` (meta) por **`tcFn`** (object) allí donde el argumento pueda ser abstracto
(la lista de conclusiones / el testigo). Piezas concretas:

1. **Constructores de código `tcFn`‑based** para cada forma que emite el tracking: `inFormCodeFn`
   (ya existe, para `In`) + análogos para `chainOk`/`land`/`lineOk`/`allIn`/`runFn`, con sus
   **congruencias** (patrón `prf_congr_inFormCodeFn`) y **clausura** (`liftFormula_provFromCode`).
2. **`prf_tc_cons`/`prf_congr_tcFn`** (ya existen, computan/congruencian `tcFn` ABSTRACTAMENTE) son
   el motor: `tcFn (cons a b)` se expresa por `tcFn a`, `tcFn b` sin exigir que sean códigos.
3. **`runFn_trackₜ`/`chainOk_trackₜ`**: espejo de los 19 casos pero produciendo `provFromCode`
   de códigos `tcFn`. El caso base y el paso usan los combinadores rastreados (§10.3).
4. **`repr_pos'_prfₜ`**: ensamblaje final. `#print axioms` esperado = `[propext, choice, Quot.sound,
   prf_inAxC]` (igual que `repr_pos'_prf`).

### 10.3 Combinadores rastreados (F1, ahora sí sobre D1ₜ)

Con D1ₜ disponible, `pcc_in_head/tail/nil` y `pcc_chainOk_*` en versión
`provFromCode(inFormCodeFn (tcFn·)(tcFn·))` se derivan (ya no stuck, porque D1ₜ emite `tcFn`).
Luego **`hI_tracked`/`hC_tracked`** por inducción object sobre `p` (`prf_list_induction`), con el
consecuente rastreado (§4.4). Cierre `d3_prf` (∃‑intro con `pcc_exIntro_code`, ∧‑intro rastreado)
→ punto fijo (`godelC_fixedpoint`) + necesitación → **`goedel_second_prf`** → limpieza F7.

### 10.4 Orden de commits (cada uno verde)

1. `liftFormula_provFromCode` ✅ (commit `fac8668`)
2. **constructores `tcFn`‑based** (`atom2CodeFn` + puente/`inFormCodeFn_eq_atom2`/congruencia/
   clausura/transporte + `chainOkCodeFn`/`allInCodeFn`) ✅ (commit `7fb9052`)
3. **`runFn_trackₜ`/`chainOk_trackₜ`** ⏳ SIGUIENTE (el port profundo, semánticamente sutil):
   espejo de `prf_runFn_track`/`prf_chainOk_track` (19 casos) de `Representability2Prf`, pero el
   código de la conclusión/lista se construye con `atom2CodeFn`+`tcFn` (object) en vez de
   `formCode`/`termCode` (meta). Aquí se decide la semántica: el testigo se rastrea por `tcFn`
   (no se congela como `varc 0`). Usa `prf_tc_cons`/`prf_congr_tcFn` (abstractos) + los
   constructores del paso 2.
4. `repr_pos'_prfₜ` (D1ₜ) → 5. combinadores rastreados → 6. `hI/hC_tracked` → 7. `d3_prf` →
   8. `goedel_second_prf` → 9. F7.

---

## 11 · Investigación de atajos (2026‑07‑05c) — resultado: NO hay atajo; la vía es la Σ₁‑completitud estándar

Antes de embarcar la construcción estándar se investigaron a fondo posibles atajos. **Resultado
riguroso: D3 es irreducible a D1/D2 y el enfoque `tcFn` no cierra.** Detalle:

### 11.1 El «atajo por teorema de deducción» es IMPOSIBLE (verificado)

Tentación: en `con_imp_godel'`, `imp_intro (fun hpg => … d3 …)` usa `hpg : ⊢ provCodeC' G` como
hipótesis; ¿podría `d3 G` sustituirse por D1 (`repr_pos'`) aplicada a `hpg`? **No.** D1 tiene tipo
**`repr_pos'_prf (h : Prf φ) : Prf (provCodeC' φ)`** y `repr_pos' (h : Prf φ) : ⊢ provCodeC' φ` —
la entrada es un **`Prf` CERRADO** (derivación finitaria sin contexto). `hpg` es una **hipótesis de
contexto** (deducción), no un `Prf` cerrado. La versión con contexto de D1 —`PrfH Γ φ → PrfH Γ
(provCodeC' φ)`— **es FALSA**: `φ` derivable DESDE una hipótesis no implica `provCodeC' φ` (que
afirma que `φ` tiene una prueba CERRADA). Justo esa brecha «hipótesis ⇒ prueba cerrada» ES el
contenido de D3 (D1 formalizada). Conclusión: **D3 no se deriva de D1/D2/deducción** (coherente con
que Gödel II necesita HBL completo / Löb; hecho estándar).

### 11.2 Por qué `tcFn` (Opción A §10) NO cierra la inducción abstracta

Sondeo del caso cabeza de `hI_tracked` (§10.3): el consecuente rastreado
`provFromCode(atom2CodeFn in_sym (tcFn ⌜φ⌝)(tcFn (cons h R)))` codifica una fórmula identificable
con el teorema `In ⌜φ⌝ (cons h R)` **sólo si** `tcFn (cons h R) =eq termCode (cons h R)` — **stuck
para `R` abstracto** (`tcFn` NO tiene ecuación de variable: sólo `zero`/`succ`/`cons`, verificado).
`prf_tc_cons` computa la ESTRUCTURA de `tcFn(cons h R)` abstractamente, pero no salva la igualdad
con `termCode`. ⇒ `tcFn` reflejaría una fórmula mal identificada → `provFromCode` indemostrable.
**El enfoque `tcFn` de §10 queda descartado para el paso inductivo abstracto.** (Los constructores
`atom2CodeFn`, `7fb9052`, siguen siendo infraestructura válida —congruencia/clausura de códigos—.)

### 11.3 La vía genuina: Σ₁‑completitud provable estándar (`substfc` + `num`)

Es la D3 de libro (Hilbert‑Bernays). **Clave que la distingue de `tcFn`:** `substfc`/`substtc`
**SÍ tiene ecuaciones de recursión para variables** (`ax_substtc_var_eq/gt/lt`, `ax_liftc_var_*`,
verificado en `Minimal/Axioms`), justo lo que falta a `tcFn`. Eso permite manipular el código
numeral‑sustituido `substfc 0 (num p) ⌜θ⌝` para `p` abstracto en la inducción.

Ingredientes (✅ = ya existe en el repo):

- ✅ `substfc` + ecuaciones (incl. variables) + `prf_substFormula_arith` (`ArithPrf`).
- ✅ `pcc_exIntro_code` (∃‑intro interno a nivel código) para el paso `Prov(⌜θ(ṗ)⌝) → Prov(⌜∃p θ⌝)`.
- ✅ inducción object `prf_list_induction` (`listInd`).
- ✅ reflexión de `In` para testigos CONCRETOS (`pcc_in_runFn_objList`) — base del caso Δ₀ atómico.
- ❓ **`num` (función object «numeral de»)** con `num(código) =eq numeral‑que‑representa‑ese‑código`
  y sus ecuaciones — **a construir** (o reusar `numeral`/`tcFn` restringido a numerales, `prf_tc_numeral`).
- ❌ **provable Δ₀‑completitud del verificador** `⊢ ∀p (δ(φ,p) → Prov(⌜δ(φ,ṗ)⌝))`, `δ = chainOk ∧ In`,
  por inducción sobre `p` con `substfc`‑var‑equations — **el núcleo grande pendiente**.
- ❌ ensamblaje `d3_prf` + `goedel_second_prf`.

**Sutileza a resolver primero (bloqueante de diseño):** el testigo `p` es una LISTA object
(`cons`/`nil`); `num` (numeral‑de) lo aplana a un numeral unario y `runFn nil (numeral …)` NO
reduce (runFn recurre sobre `cons`/`nil`). Hay que decidir la codificación del testigo‑como‑número
(β‑función / secuencia) para que `runFn`/`chainOk`/`In` operen sobre él vía decodificación
representable — o reformular `δ` sobre números. **Esta decisión de codificación es el primer paso
de §11 y debe fijarse antes de codificar.**

### 11.4 Marco honesto del estado

El proyecto ya tiene **Gödel I REAL sin postulados**, **D1 y D2 REALES**, y **Gödel II módulo un
único axioma D3 claramente marcado** (`GodelTwo.goedel_second'`). D3 = Σ₁‑completitud provable es
**notoriamente la pieza más dura** de formalizar Gödel II (lo es también en Isabelle/Coq). El
estado actual es excelente y publicable. Cerrar D3 es un desarrollo grande (varias sesiones) cuyo
primer paso NO es código sino la **decisión de codificación del testigo (§11.3 sutileza)**.

---

## 12 · Diseño de la codificación del testigo (2026‑07‑05d)

**Encargo:** fijar cómo se codifica el testigo (cadena de prueba) para la Σ₁‑completitud provable.

### 12.1 Hallazgo central: la codificación del testigo ≡ la representación del verificador

La decisión NO es aislable. La Σ₁‑completitud provable estándar exige que `δ(φ,p)` sea **genuinamente
Δ₀‑sobre‑números** (cuantificadores acotados sobre una secuencia codificada por número), porque la
inducción de provable Δ₀‑completitud es **estructural sobre la fórmula** y su caso atómico usa
**evaluación provable de términos numéricos**. Pero nuestro verificador (`runFn`/`chainOk`/`In`/`carc`/
`cdrc`) es **recursión estructural sobre listas `cons`/`nil`**, SIN indexación numérica ni
cuantificación acotada (verificado: sólo existen `carc`/`cdrc`, no `len`/`nth`/`_lt_len`). Es decir,
`δ` **no está en forma Δ₀‑sobre‑números**, y la maquinaria estándar no se le aplica directamente.

### 12.2 Por qué la inducción de listas naíf (mantener el testigo‑lista) NO cierra

Intento: probar `⊢ ∀p (In ⌜φ⌝ (runFn nil p) → provFromCode(substfc 0 (tcFn p) ⌜In ⌜φ⌝ (runFn nil ·)⌝))`
por inducción object sobre `p`. En **concreto** `p₀` el consecuente =eq `provCodeC'(In ⌜φ⌝ (runFn nil p₀))`
(vía `substFormula_arith` + `tcFn p₀ =eq termCode p₀`), demostrable (`pcc_in_runFn_objList`). Pero el
**paso** `p = cons line rest`, caso cola, requiere pasar de la IH
`provFromCode(substfc 0 (tcFn rest) ⌜body⌝)` al objetivo `provFromCode(substfc 0 (tcFn (cons line rest)) ⌜body⌝)`:
son códigos con **testigos DISTINTOS** (`tcFn rest` vs `tcFn (cons line rest)`) → codifican fórmulas
distintas (`In ⌜φ⌝ (runFn nil rest)` vs `In ⌜φ⌝ (runFn nil (cons line rest))`). `pcc_imp` (D2+D1) sube
implicaciones object PERO sobre el **mismo** código sustituido; aquí el testigo cambia, así que no aplica.
La monotonía object `In x (runFn nil rest) ⇒ In x (runFn nil (cons line rest))` existe, pero su reflexión
mezcla dos sustituciones‑testigo → no hay combinador que lo cierre. **Confirmado: la vía testigo‑lista +
`substfc`/`tcFn` no cierra el paso inductivo** (mismo muro que §11.2, ahora en el paso cola).

### 12.3 Opciones de codificación (con tradeoffs honestos)

| Opción | Idea | Coste | Riesgo |
|---|---|---|---|
| **12‑A · β‑función / secuencia** | Codificar la cadena como UN número (secuencia Gödel β), re‑expresar `runFn`/`chainOk`/`In`/`carc` como fórmulas **Δ₀‑sobre‑números** (∃/∀ acotados + `β`). Aplicar provable Δ₀‑completitud estándar. | **Alto**: nuevo verificador numérico + re‑derivar D1 para él (o probar equivalencia con el de listas). | Bajo (es la construcción de libro; **funciona seguro**). |
| **12‑B · testigo‑lista + inducción** | Mantener listas, inducción object sobre `p`. | Medio | **Alto → descartada** (§12.2: paso cola no cierra). |
| **12‑C · tracking por POSICIÓN** | Reflejar `In ⌜φ⌝ (runFn nil p)` vía la **posición** `i` de `⌜φ⌝` (∃ acotado, testigo = número `i`, que `num` maneja limpio), no el testigo‑lista entero. | Medio‑alto: exige `len`/`nth` object + su Δ₀‑ización + relación con `carc`/`cdrc`. | Medio (aún necesita indexación numérica que no existe). |

### 12.4 Recomendación

**12‑A (β‑función)** es la única con riesgo bajo y es la construcción canónica. Implica reconocer que
**cerrar D3 real = dotar al verificador de una capa numérica Δ₀** (indexación acotada + β), sobre la
que la Σ₁‑completitud provable es mecánica‑estándar. Es un desarrollo grande (varias sesiones) y de
hecho **coincide en gran parte con la Opción 3** (reformular el verificador sobre números) — la
codificación del testigo y la representación del verificador son la misma decisión (§12.1).

**Plan 12‑A por fases (cada una verde):**

1. **Capa numérica de listas**: `lenc`/`nthc` object (longitud/índice de una lista‑código) + ecuaciones
   (recursión `carc`/`cdrc`) + `In x L ⇔ ∃i<lenc L. nthc L i =eq x` (caracterización acotada).
2. **β / secuencia**: reusar la codificación existente (las listas YA son números‑código) — probar que
   `runFn`/`chainOk` se expresan con `∃/∀` acotados sobre índices (Δ₀).
3. **`num` (numeral‑de) + `substfc`‑var‑equations**: provable evaluación de términos y provable
   Δ₀‑completitud atómica (`=`,`<`,`In`‑acotado).
4. **Inducción estructural Δ₀‑completitud** → `⊢ ∀p (δ(φ,p) → Prov(⌜δ(φ,ṗ)⌝))`.
5. **∃‑intro** (`pcc_exIntro_code`) → `d3_prf` → `goedel_second_prf` → F7.

**Alternativa (§11.4):** si el coste de 12‑A no compensa, consolidar Gödel II módulo el axioma D3 es un
cierre honesto y publicable.

---

## 13 · SONDEO de la Fase 2 (2026‑07‑08) — veredicto: **NO hace falta β‑función**

**Pregunta.** §12.3 temía que `runFn`, al ser **recursión con acumulador**, exigiera codificación de
secuencias (β‑función) para expresarse con cuantificadores acotados. Era el único paso del plan 12‑A
con riesgo de diseño sin verificar.

### 13.1 Resultado (verificado en código, `Meta/RunFnBoundedPrf.lean`)

**`runFn nil p` no es una recursión con acumulador: es el *map* de `carc` sobre `p`.** Probado:

```lean
theorem prf_runFn_nil_cons (line rest) :        -- ← LEMA DECISIVO
  Prf (runFn nil (cons line rest) =eq cons (carc line) (runFn nil rest))
theorem prf_lenc_runFn (p) : Prf (lenc (runFn nil p) =eq lenc p)
```

(cadena: `prf_runFn_cons` → `prf_concat_nil_eq` → **`prf_runFn_weaken`** (saca el acumulador fuera)
→ `prf_concat_cons_eq`. `#print axioms` = `[propext, choice, Quot.sound]`.)

**Consecuencia:** el acumulador **nunca hay que construirlo ni codificarlo**.

- `In x (runFn nil p)` queda **acotado por `lenc p`** (vía `prf_In_iff_boundedIn` + `prf_lenc_runFn`).
- En `chainOk`, el acumulador de la línea `i` es «las conclusiones anteriores», y sólo se usa a
  través de `In y (·)`; eso se reescribe como **`∃ k < i. carc (nthc p k) =eq y`** — acotado sobre `p`.

Es la formulación Δ₀ clásica de «demostración = sucesión de líneas, cada una justificada por
líneas anteriores». **Sin β‑función, sin capa de secuencias.** El riesgo de §12.3 queda **cerrado**.

### 13.2 Lo que SÍ queda de Fase 2 (trabajo real, patrón conocido)

1. **`nthc (runFn nil p) i =eq carc (nthc p i)`** (para `i < lenc p`). Requiere inducción con **`∀i`
   interno** en el predicado inductivo → patrón `norm32`/`norm_s`/confinación‑`qconf` **ya usado tres
   veces en `ChainPrf.lean`** (`prf_runFn_concat`, `prf_chainOk_mono_imp`, `prf_runFn_weaken`).
2. **Reformulación acotada de `chainOk nil p`**:
   `∀ i < lenc p. ( lineWF (nthc p i) ∧ ∀ j < lenc (premsOf (nthc p i)). ∃ k < i. carc (nthc p k) =eq nthc (premsOf (nthc p i)) j )`
   y probar la equivalencia con `chainOk nil p` por inducción. El acumulador‑prefijo se elimina
   con el `∃ k < i`. **Esta equivalencia es el único punto que aún no he verificado en código**
   (no veo obstrucción, pero no está probado).

### 13.3 Corrección a §12.3/§12.4

La recomendación 12‑A sigue en pie, pero **su descripción como «β‑función» era pesimista**: la capa
numérica de listas (`lenc`/`nthc`, ya hecha en fase 1) es suficiente. Léase §12.4 fase 2 como
«reformulación acotada» y no como «codificación de secuencias».

---

## 14 · Fase 2: lado `In` CERRADO; plan preciso del lado `chainOk`

### 14.1 Lado `In` — hecho (`Meta/RunFnBoundedPrf.lean`, commits `4685366`/`ffbcdb9`/`05cc4ab`)

```lean
prf_runFn_nil_cons : runFn nil (cons line rest) =eq cons (carc line) (runFn nil rest)
prf_lenc_runFn     : lenc (runFn nil p) =eq lenc p
prf_nthc_runFn     : i < lenc p ⇒ nthc (runFn nil p) i =eq carc (nthc p i)
prf_In_runFn_iff   : In y (runFn nil p) ⇔ ∃ i < lenc p. carc (nthc p i) =eq y   -- ← payoff
```

Todos `[propext, choice, Quot.sound]`. La cota es **`lenc p`**: acotado sobre `p` directamente.

`prf_nthc_runFn` usó el patrón de **`∀i` interno** (la HI se aplica en `pred i`) → 3 binders en el
`step` + confinación `Prf.qconf` + `PrfH_spec`, igual que `prf_runFn_concat` en `ChainPrf`.

### 14.2 Lado `chainOk` — la forma acotada objetivo

El acumulador se elimina **generalizando en `c`**: cada premisa está o bien ya en el contexto
inicial `c`, o bien es la conclusión de una línea **anterior**.

```text
chainOkB c p  :=  ∀ i < lenc p.
    ( lineWF (nthc p i)
      ∧ ∀ j < lenc (premsOf (nthc p i)).
          ( In (nthc (premsOf (nthc p i)) j) c
            ∨ ∃ k < i. carc (nthc p k) =eq nthc (premsOf (nthc p i)) j ) )
```

**Objetivo:** `chainOk c p ⇔ chainOkB c p` (y para `c = nil` el disyunto izquierdo es falso,
quedando la forma Δ₀ pura). Por inducción de listas sobre `p` con **`∀c` interno** (patrón `qconf`).

### 14.3 Sub‑lemas necesarios (todos con patrón ya validado)

1. **`allIn c L ⇔ ∀ j < lenc L. In (nthc L j) c`** (caracterización acotada de `allIn`; espejo ∀ de
   `prf_In_iff_boundedIn`). Piezas: `prf_boundedAllIn_head` (spec en `0`), `prf_boundedAllIn_tail`
   (spec en `σj`), `prf_boundedAllIn_cons`, más las dos inducciones.
   **Nota de patrón:** para probar un `∀` como CONSECUENTE bajo contexto, usar **`Prf.qconf`**
   (`A ⇒ ∀C` desde `∀(↑A ⇒ C)`), nunca `PrfH.gen` (liftea el contexto). Para instanciar el `∀` de
   una HIPÓTESIS, `PrfH_spec` (no liftea).
2. **`In y (concat c (cons x nil)) ⇔ In y c ∨ y =eq x`** (de `ax_L3_in_concat` + `ax_L2`).
3. **Split del `∃k < σj`**: `(∃ k < σj. carc (nthc (cons line rest) k) =eq y)
   ⇔ (carc line =eq y ∨ ∃ k < j. carc (nthc rest k) =eq y)` (case‑split de `k` con
   `prf_zero_or_eq_succ_pred` + `prf_nthc_zero`/`prf_nthc_succ`).
4. **Inducción principal** `∀c. (chainOk c p ⇔ chainOkB c p)`, paso `cons` usando
   `prf_chainOk_cons` (`chainOk c (cons line rest) ⇔ lineOk c line ∧ chainOk (c++[carc line]) rest`)
   + (1) + (2) + (3): el índice `i = 0` da `lineOk c line`, e `i = σj` reindexa a `chainOkB (c++[carc line]) rest`.

**No veo obstrucción** en ninguno de los cuatro; (4) es el más pesado (dos niveles de
cuantificación acotada dentro del predicado inductivo). **Aún NO verificado en código.**

### 14.4 Lecciones De Bruijn acumuladas (reusar)

- `∃`‑elim de una **hipótesis** → lema `Prf` autónomo con **`prf_ex_elim_imp`** (lift simple).
  Nunca `PrfH_ex_elim` (liftea el contexto → doble lift).
- `∀`‑intro como **consecuente** → **`Prf.qconf`**. `∀`‑elim de una **hipótesis** → `PrfH_spec`.
- Case‑split de un índice bajo `PrfH` **sin `∃`** → `prf_zero_or_eq_succ_pred` (testigo `pred i`).
- Empujar `liftFormula`/`substFormula` a través de un predicado con `∃`/`∀` interno requiere un
  lema propio (`liftFormula_boundedIn_gen`, `substFormula_boundedIn`, `liftFormula_boundedCarcIn`):
  **no es defeq** (`liftTerm 1 (liftTerm 0 ·)` vs `liftTerm 0 (liftTerm 0 ·)` los iguala
  `FOL.liftTerm_comm_zero`, que es teorema).
- En un `have`, `PrfH _ (…)` **no infiere Γ**: nombrar el contexto con `let`.

---

## 15 · Fase 3 (arranque, 2026‑07‑09): D3 reducida a reflejar la forma Δ₀ ACOTADA

Con la **fase 2 completa**, el §11.3 («`num` + evaluación provable») se re‑ancla en el mundo
acotado. La D3 reducida `d3_prf_of_sigma1` pedía dos lemas de **Σ₁‑completitud provable**:

```text
hI : ∀ x L,  Prf (In x L      ⇒ provCodeC' (In x L))
hC : ∀ p,    Prf (chainOk nil p ⇒ provCodeC' (chainOk nil p))
```

### 15.1 Puente arquitectónico — HECHO (`Meta/Sigma1BoundedPrf.lean`)

Como la fase 1/2 dio los `⇔` (`prf_In_iff_boundedIn`, `prf_chainOk_iff_chainOkB`) y `pcc_imp`
sube implicaciones object a `provCodeC'` (vía D2+D1), `hI`/`hC` se **reducen a reflejar la forma
acotada**:

```lean
prf_hI_of_reflect_boundedIn (hbI : ∀ x L, Prf (boundedIn x L ⇒ provCodeC' (boundedIn x L)))
  : ∀ x L, Prf (In x L ⇒ provCodeC' (In x L))
prf_hC_of_reflect_chainOkB  (hbC : ∀ p, Prf (chainOkB nil p ⇒ provCodeC' (chainOkB nil p)))
  : ∀ p, Prf (chainOk nil p ⇒ provCodeC' (chainOk nil p))
d3_prf_of_reflect_bounded (φ) (hbC) (hbI)  -- = d3_prf, reduciendo a la forma Δ₀ acotada
```

`[propext, choice, Quot.sound, prf_inAxC]`. **Payoff:** basta reflejar `boundedIn`/`chainOkB`.

### 15.2 Dónde vive ahora la obstrucción de Tarski (y qué la resuelve)

Reflejar `boundedIn x L` = `∃ i < lenc L. nthc L i =eq x` **no dissuelve** la obstrucción, la
**reubica en el átomo** `nthc L i =eq x` (para `L`, `x` abstractos, `formCode(nthc L i =eq x)`
contiene `termCode (nthc L i)`, **meta‑stuck**). Y ESTO es exactamente lo que resuelven las
**ecuaciones de variable de `substfc`** (`ax_substtc_var_eq/gt/lt`, ausentes en `tcFn`): permiten
reflejar el átomo tras sustituir el numeral del testigo. Por eso el §11.3 («`num` + provable
evaluation») sigue siendo la vía correcta — pero ahora aplicado **solo a los átomos** de la forma
acotada, no a un verificador numérico entero.

### 15.3 Reflexión atómica RASTREADA — `=eq` HECHO (`Meta/Sigma1AtomPrf.lean`)

**Hallazgo clave (confirmado en código):** la reflexión de `t =eq u` para `t`, `u` **abstractos**
es **imposible libre de muro** (Tarski): `termCode t =eq termCode u` NO se sigue de `t =eq u`
(`termCode` no tiene congruencia object). La salida Hilbert‑Bernays es **rastrear** los argumentos
con `tcFn` (que SÍ tiene congruencia, `prf_congr_tcFn`) y **descargar** el puente
`tcFn t =eq termCode t` cuando `t` es numeral (`prf_tc_numeral`) — en la inducción de fase 5. Esto
espeja exactamente el toolkit rastreado de `In` (`prf_provCodeC'_In_of_tracked`, `Sigma1CorePrf`).

Toolkit `=eq` entregado (`[propext, choice, Quot.sound]`, la reflexividad `+ prf_inAxC`):

```lean
def eqCodeFn (a b) := ⟨4, a, b⟩                       -- eqCodeFn (termCode t)(termCode u) = formCode(t=u)
prf_congr_eqCodeFn / prf_provFromCode_eq_congr        -- congruencia + transporte (Leibniz object)
liftTerm_eqCodeFn / liftFormula_provFromCode_eq       -- clausuras
prf_provCodeC'_eq_of_tracked (ht : tc =eq termCode t)(hu)(h : provFromCode(eqCodeFn tc uc))
  : provCodeC'(t =eq u)                               -- reflexión rastreada (espejo de In)
prf_provFromCode_eqCodeFn_refl_of_tracked (ht : tc =eq termCode t) : provFromCode(eqCodeFn tc tc)
```

### 15.4 Reflexividad LIBRE DE MURO — HECHA, y el átomo `=eq` cerrado sin muro

**Idea que lo desbloquea:** el verificador comprueba `lineWF` **estructuralmente**. La línea‑axioma
EQREFL es `⟨concl, 12, t⟩` y su condición es (`prf_lineWF_eqrefl`):

```text
lineWF ⟨concl, 12, t⟩  ⇔  concl =eq eqc t t
```

y `eqc a b` es **literalmente** `eqCodeFn a b` (`numeral 4 = σ⁴0`). Tomando `concl := eqCodeFn c c`
y `t := c`, la condición es **pura reflexividad** (`prf_refl`), válida para `c` **arbitrario**:
`termCode` no aparece por ningún lado. El testigo es la cadena de **una sola línea**
`p := [⟨eqCodeFn c c, 12, c⟩]`.

```lean
def eqreflLine (c) := cons (eqCodeFn c c) (cons (numeralM 12) (cons c nil))
prf_lineOk_eqrefl / prf_chainOk_eqrefl / prf_in_runFn_eqrefl
prf_provFromCode_intro (d p) (chainOk nil p) (In d (runFn nil p)) : provFromCode d
prf_provFromCode_eqCodeFn_refl (c) : Prf (provFromCode (eqCodeFn c c))   -- ← LIBRE DE MURO
```

**Payoff — el átomo `=eq` queda cerrado sin muro** al nivel del código rastreado: de `t =eq u` sale
`tcFn t =eq tcFn u` (congruencia de `tcFn`) y se transporta por Leibniz object sobre la base
reflexiva:

```lean
PrfH_congr_tcFn / PrfH_congr_eqCodeFn
pcc_eq_tracked (t u) : Prf ((t =eq u) ⇒ provFromCode (eqCodeFn (tcFn t) (tcFn u)))   -- LIBRE DE MURO
pcc_eq_of_tc_bridge (t u) (ht : tcFn t =eq termCode t) (hu) : Prf ((t =eq u) ⇒ provCodeC' (t =eq u))
```

Los tres: `#print axioms = [propext, choice, Quot.sound]` — al no pasar ya por `repr_pos'`,
**desaparece incluso la dependencia de `prf_inAxC`**.

**El muro de Tarski queda confinado al último paso** (`pcc_eq_of_tc_bridge`): el puente
`tcFn t =eq termCode t`, descargable con **numerales** (`prf_tc_numeral`) en la inducción de fase 5.
Eso es exactamente lo que la construcción de Hilbert‑Bernays predice, y ya no hay nada más que
resolver en el átomo de igualdad.

### 15.5 Lo que queda de fase 3‑5 (orden)

1. **Átomos `<` y `lineWF`**: `<` = `∃k. a+σk=b` (no es átomo — se reduce a `=eq` + `∃` acotado);
   `lineWF t` es un átomo‑1 → constructor `atom1CodeFn` análogo a `eqCodeFn`. El átomo `In` ya tiene
   su toolkit (`Sigma1CorePrf`).
2. **Reflexión de cuantificadores acotados** (fase 4): `∀ i < b. provCodeC' θ(i) ⊢ provCodeC'(∀ i<b.θ)`
   y la versión `∃` (con `pcc_exIntro_code`).
3. **Inducción estructural** sobre `boundedIn`/`chainOkB` (fase 5) ensamblando 1‑2, descargando el
   puente `tcFn·=eq termCode·` con `prf_tc_numeral` → `hbI`/`hbC` → `d3_prf_of_reflect_bounded`
   → `d3_prf` → `goedel_second_prf`.

**Obstrucción encontrada en (1)** — ver §16.

---

## 16 · OBSTRUCCIÓN: `lineWF` / `premsOf` no están determinados (falta axioma de inversión)

**Hallazgo (2026‑07‑10), verificado sobre `Minimal/Axioms.lean`.** Al atacar el átomo `lineWF` de
`chainOkB` aparece una obstrucción **real**, distinta de la de Tarski.

### 16.1 El hecho

- `lineWF t := Formula.atom "lineWF" [t]` es un **átomo primitivo**.
- Sus **21 axiomas** (`ax_lineWF_mp`, …, `ax_lineWF_listInd`) son bicondicionales **indexados por la
  etiqueta de regla**: `lineWF ⟨concl, numeralM k, args…⟩ ⇔ <condición estructural>`, con
  `k ∈ {0,…,20}`.
- **NO existe axioma de inversión / completitud** (`lineWF t ⇒ la etiqueta de t está en {0..20}`).
- `premsOf` (símbolo de función) tiene exactamente el mismo patrón: 21 ecuaciones por etiqueta, sin
  inversión.

**Consecuencia:** para una línea `t` con etiqueta fuera de `{0..20}` (p. ej. `numeralM 21`), o con
etiqueta no numeral, **`lineWF t` queda indeterminado** por los axiomas. Luego

```lean
Prf (lineWF t ⇒ provCodeC' (lineWF t))     -- ← NO derivable para `t` abstracto
```

porque de la hipótesis `lineWF t` la teoría **no puede extraer la etiqueta** de `t`, y sin etiqueta
no puede reconstruir la prueba interna de la condición estructural.

### 16.2 Por qué `chainOk` sí y `lineWF` no

`chainOk` tiene `ax_chainOk_nil` + `ax_chainOk_cons` (recursión sobre `nil`/`cons`) y el esquema
`ax_list_induction` cuantifica sobre **todo `Term`**. Por tanto `chainOk` **sí** está determinado y
su reflexión se ataca por inducción de listas. `lineWF`, en cambio, discrimina sobre un **numeral**
(la etiqueta), y no hay ningún axioma que acote ese numeral.

### 16.3 Alcance

Esto **no afecta a la solidez** de nada ya demostrado (D1/D2/Gödel I siguen intactos: sólo usan
`lineWF` sobre líneas **concretas**, con etiqueta conocida). Afecta sólo a la **reflexión de `hbC`**
(`chainOkB`), que necesita `lineWF` para líneas abstractas.

**`hbI` NO está afectado:** `boundedIn x L = ∃ i < lenc L. nthc L i =eq x` sólo contiene los átomos
`=eq` (cerrado, §15.4) y `<` (reducible a `=eq` + `∃` acotado). La rama `hbI` puede seguir sin tocar
la axiomática.

### 16.4 Arreglo mínimo propuesto

Añadir **un** axioma de inversión a `Minimal/Axioms.lean` (precedente exacto: la capa `lenc`/`nthc`
de la fase 1a — es un `def ax_*` de la teoría objeto, **no** una declaración `axiom` de Lean, así que
los 7 `axiom` de `AXIOMS.md` **no cambian**):

```lean
def ax_lineWF_inv : Formula :=      -- ∀line. lineWF line ⇒ (⋁_{k=0}^{20} nthc line 1 =eq numeralM k)
```

Con él, `lineWF` queda **totalmente determinado** (inversión + los 21 bicondicionales), `premsOf`
también (conocida la etiqueta, su ecuación aplica), y la reflexión de `lineWF t` se reduce a reflejar
una **disyunción finita de átomos `=eq`** — que ya sabemos hacer (`pcc_eq_tracked`).

Debe añadirse a **`axioms` y `codingAxioms`** (para preservar `axioms_eq` por `rfl`), igual que en
la fase 1a.

**Es una decisión matemática (amplía la teoría objeto): requiere sanción explícita.**

### 16.5 RESUELTO (2026‑07‑10, sancionado)

`ax_lineWF_inv` añadido a `Minimal/Axioms.lean` (`lineTag`, `tagDisj`, y el axioma), al final de
`axioms` **y** `codingAxioms`. Cierre `Prf`: **`prf_lineWF_inv (line) : Prf (lineWF line ⇒ tagDisj line 20)`**
(`Meta/Sigma1AtomPrf.lean`).

Verificación tras tocar el núcleo (build 76 jobs verde):

- `axioms_eq : axioms = coreAxioms ++ codingAxioms` sigue siendo **`rfl`**.
- **La cadena real NO cambia**: `goedel_second'` sigue citando sólo `d3`; `d2_prf` limpio;
  `repr_pos'_prf` = estándar + `prf_inAxC`.
- Es un `def ax_*` de la teoría objeto: **los 7 `axiom` de Lean de `AXIOMS.md` no cambian**.

---

## 17 · SEGUNDA OBSTRUCCIÓN: el `∃`‑intro de código exige testigo CERRADO

**Hallazgo (2026‑07‑10).** Al arrancar la rama `hbI` (que creíamos libre) aparece un bloqueo:

```lean
pcc_exIntro_code (Ac w) (hAc : ∀ c, liftTerm c Ac = Ac) (hw : ∀ c, liftTerm c w = w)
  : Prf (provFromCode (substfc zero w Ac) ⇒ provFromCode (exc Ac))
```

La hipótesis **`hw` exige que el código del testigo `w` sea cerrado**. Pero en
`hbI : ∀ x L, Prf (boundedIn x L ⇒ provCodeC' (boundedIn x L))`, tras el `∃`‑elim del antecedente
(`prf_ex_elim_imp`) el testigo es la variable ligada `#0`, y `tcFn #0` **no es cerrado** ⇒ `hw` no se
descarga. **Es el mismo muro que RIESGO‑1** (`Meta/Sigma1TrackedPrf.lean`), reaparecido en la forma
acotada. Corrige la afirmación de §16.3 («`hbI` no bloqueado»): **ambas ramas, `hbI` y `hbC`, pasan
por aquí.**

### 17.1 Por qué es reparable (no es Tarski)

`hw` se usa en **un solo punto** del proof de `pcc_exIntro_code`: colapsar
`liftTerm 0 (substfc zero w Ac)` en el antecedente (vía `liftTerm_substfc`). Sin `w` cerrado eso no
colapsa, pero **sí es expresable**:

```text
liftTerm 0 (substfc zero w Ac)  =  substfc zero (liftTerm 0 w) Ac        (Ac cerrado por hAc)
```

Es decir: en vez de *colapsar* el lift del testigo, hay que **arrastrarlo**. La línea‑axioma Q2 que
el testigo construye pasa a ser `⟨implc (substfc zero (↑w) Ac) (exc Ac), 10, Ac, ↑w⟩`, y la
conclusión `exc Ac` sigue siendo cerrada (que es lo único que el objetivo `provFromCode (exc Ac)`
necesita). Nada aquí toca `termCode` ni la obstrucción de Tarski.

### 17.2 RESUELTA (2026‑07‑10): `pcc_exIntro_code'` — `hw` era innecesaria

```lean
pcc_exIntro_code' (Ac w) (hAc : ∀ c, liftTerm c Ac = Ac)   -- ¡SIN hw!
  : Prf (provFromCode (substfc zero w Ac) ⇒ provFromCode (exc Ac))
```

La pieza que lo hace posible:

```lean
liftTerm_substfc_open (Ac) (hAc) (w) : ∀ c, liftTerm c (substfc zero w Ac) = substfc zero (liftTerm c w) Ac
```

El lift **atraviesa** `substfc zero · Ac` y queda sobre el testigo (`zero` es cerrado; `Ac` lo es por
`hAc`). Con eso, el contexto tras `prf_ex_elim_imp` es **idéntico** al de antes con `w' := liftTerm 0 w`,
y el ensamblaje `p ++ [q2line, mpline]` pasa **verbatim** (la línea‑axioma Q2 `prf_lineOk_q2 Cp Ac w'`
admite cualquier testigo). La conclusión `exc Ac` sigue cerrada, que es lo único que el objetivo
`provFromCode (exc Ac)` necesita.

`#print axioms pcc_exIntro_code' = [propext, choice, Quot.sound]`. El antiguo `pcc_exIntro_code` se
conserva como **corolario** (su `hw` queda como argumento no usado): retrocompatible, build verde.

**Verificado explícitamente** que el testigo puede ser una **variable ligada** y su **código
rastreado**:

```lean
example (Ac) (hAc) : Prf (provFromCode (substfc zero (tcFn #0) Ac) ⇒ provFromCode (exc Ac)) :=
  pcc_exIntro_code' Ac (tcFn #0) hAc          -- ✓ typechequea
```

### 17.3 Qué cae exactamente de RIESGO‑1 (con precisión)

RIESGO‑1 (§4.2/§11.2) tenía **dos** mitades:

| Mitad | Estado |
|---|---|
| (a) `tcFn #0` no es cerrado ⇒ `hw` falla | ✅ **DISUELTA** por `pcc_exIntro_code'` |
| (b) transporte `tcFn L =eq termCode L` (Tarski) | ⚠ **sigue viva**, pero **confinada** al último paso (§15.4), descargable con numerales (`prf_tc_numeral`) en la inducción de fase 5 |

No hay sobre‑afirmación: (b) es la obstrucción de Tarski genuina y su lugar correcto es el puente.

### 17.4 Camino libre

Con §16.5 (`ax_lineWF_inv`) y §17.2 (`pcc_exIntro_code'`), **no queda obstrucción conocida**:

1. **`hbI`** (`boundedIn`): átomos `=eq` ✅ (§15.4) + `<` (reducible a `=eq` + `∃` acotado) + `∃`‑intro
   de código con testigo abierto ✅.
2. **`hbC`** (`chainOkB`): además `lineWF` ✅ (§16.5) + `In` ✅ (`Sigma1CorePrf`).
3. Reflexión de cuantificadores acotados (∀/∃) + inducción estructural (fase 5, con `prf_tc_numeral`
   descargando el puente (b)) → `d3_prf_of_reflect_bounded` → `d3_prf` → `goedel_second_prf`.

---

## 18 · La reflexión de `<` NO es un ladrillo pequeño: aterriza en la evaluación provable

**Sondeo (2026‑07‑10), verificado compilando.** `lt a b := .atom lt_sym [a, b]`, definido por
`ax13_lt_def : lt a b ⇔ ∃k. a + σk = b`. Parecía que reflejar `<` era inmediato: `=eq` está cerrado
libre de muro (§15.4) y el `∃`‑intro de código admite testigo abierto (§17.2). **No lo es.**

### 18.1 Lo que SÍ tenemos (ambos typechequean)

```lean
-- (A) reflexión rastreada de la igualdad, LIBRE DE MURO
pcc_eq_tracked (add a (succ k)) b
  : Prf ((add a (succ k) =eq b) ⇒ provFromCode (eqCodeFn (tcFn (add a (succ k))) (tcFn b)))

-- (B) ∃-intro de código con testigo ABIERTO
pcc_exIntro_code' Ac (tcFn k) hAc
  : Prf (provFromCode (substfc zero (tcFn k) Ac) ⇒ provFromCode (exc Ac))
```

### 18.2 Por qué (A) no encaja en (B)

Para componerlos haría falta

```text
substfc zero (tcFn k) Ac   =eq   eqCodeFn (tcFn (add a (succ k))) (tcFn b)
```

donde `Ac` es el código del cuerpo `↑a + σ#0 = ↑b`. Pero:

- `tcFn` (= `num`, «numeral‑de») sólo tiene **tres** ecuaciones: `ax_tc_zero`, `ax_tc_succ`,
  `ax_tc_cons`. No computa sobre `add`, `nthc`, `lenc`, `runFn`, …
- **Y no debe computar sobre ellas.** `tcFn (add a (succ k))` es el código del **numeral del valor**
  `a + σk`; el cuerpo del `∃` de `ax13` necesita el código del **término simbólico** `ȧ + σj̇`.
  Son **códigos distintos**.

El puente entre ambos es precisamente

```text
⊢ Prov( ⌜ ȧ + σk̇  =  (a + σk)˙ ⌝ )
```

es decir, que la teoría objeto **demuestre internamente que la suma de numerales evalúa al numeral
de la suma**. Eso es la **evaluación provable** (`num` + provable evaluation) que §11.3 nombró como
el núcleo de la fase 3. No es un lema pequeño: se prueba por **inducción interna** sobre el numeral.

### 18.3 Consecuencia para el plan

`<` **no es un átomo aparte que reflejar**: es `∃` + `=eq` + **evaluación provable de `+`**. Por tanto
el orden correcto de las fases 3‑5 es:

1. **Evaluación provable** (fase 3, núcleo real): `⊢ Prov(⌜ṫ = v̇⌝)` para términos `t` construidos con
   los símbolos del cuerpo Δ₀ (`+`, `σ`, `lenc`, `nthc`, `carc`, `runFn`) evaluados en numerales.
   Requiere inducción interna. **Es «la bestia».**
2. **Reflexión de `<`** — corolario de (1) + `=eq` (§15.4) + `∃`‑intro de código (§17.2).
3. **Cuantificadores acotados** (∀/∃) e **inducción estructural** → `hbI`/`hbC` → `d3_prf`.

### 18.5 → ver §19: el andamiaje interno ya está construido

### 18.4 Ladrillo entregado hacia (1)

**`liftFormula_provFromCode_open (k c) : liftFormula k (provFromCode c) = provFromCode (liftTerm k c)`**
(`Meta/TrackedCorePrf.lean`) — generaliza `liftFormula_provFromCode` a **códigos abiertos**. La
necesita el **∀‑elim de código** (`prf_lineWF_q1` es estructural, igual que la línea Q2), donde el
código abierto cae en el **consecuente** — al revés que en `pcc_exIntro_code'`. El ∀‑elim de código es
imprescindible para **instanciar axiomas codificados** (p. ej. `ax13`) dentro de la prueba interna.

---

## 19 · Sistema de prueba INTERNO a nivel de código (andamiaje de la evaluación provable)

**Hecho (2026‑07‑10).** La evaluación provable necesita razonar **dentro** de la demostrabilidad, con
códigos que ya **no** son `formCode` de nada meta (salen de `substfc zero w Ac`). Se ha construido el
juego completo de reglas a nivel de código.

| Regla | Lema | Módulo | Testigo | `#print axioms` |
|---|---|---|---|---|
| `∃`‑intro (Q2) | `pcc_exIntro_code'` | `ExIntroCodePrf` | **abierto** | `[propext, choice, Quot.sound]` |
| `∀`‑elim (Q1) | `pcc_forallElim_code'` | `ForallElimCodePrf` | **abierto** | `[propext, choice, Quot.sound]` |
| MP | `pcc_mp_code` | `MpCodePrf` | — | `[propext, choice, Quot.sound]` |
| Axioma de la teoría | `pcc_axiom_inst` | `MpCodePrf` | **abierto** | `+ prf_inAxC` |

### 19.1 `pcc_forallElim_code'` — la asimetría con Q2

```lean
pcc_forallElim_code' (Ac w) (hAc : ∀ c, liftTerm c Ac = Ac)
  : Prf (provFromCode (forallc Ac) ⇒ provFromCode (substfc zero w Ac))
```

`prf_lineWF_q1 (concl A t) : lineWF ⟨concl, 9, A, t⟩ ⇔ (concl =eq implc (forallc A) (substfc zero t A))`
es **estructural** (sin `termCode`), igual que la línea Q2 ⇒ admite `A`, `t` arbitrarios. Testigo de
cadena `r = p ++ [q1line, mpline]`, espejo de `pcc_exIntro_code'`.

**Asimetría:** en Q2 el código abierto cae en el **antecedente** (se arrastra su lift, §17.1); en Q1
cae en el **consecuente**, y ahí hace falta `liftFormula_provFromCode_open` (§18.4).

### 19.2 `pcc_mp_code` — D2 para códigos arbitrarios

```lean
pcc_mp_code (Ac Bc) (hAc) (hBc)
  : Prf (provFromCode (implc Ac Bc) ⇒ (provFromCode Ac ⇒ provFromCode Bc))
```

Porte de `d2_prf` con `Ac`/`Bc` en lugar de `formCode A`/`formCode B` y las clausuras `hAc`/`hBc` en
lugar de `liftTerm_formCode`. **Escollo (mismo que `pcc_exIntro_code`):** en el `simp` posterior a
`PrfH_ex_intro` **no** hay que colapsar `liftTerm 0 Bc` — se cancela con la subst externa
`substTerm 0 r (·)`; incluir `hBc` allí rompe la prueba.

### 19.3 `pcc_axiom_inst` — instanciar axiomas codificados

```lean
pcc_axiom_inst (φ) (hmem : Formula.forall φ ∈ axioms) (w)
  : Prf (provFromCode (substfc zero w (formCode φ)))
```

(usa `formCode (Formula.forall φ) = forallc (formCode φ)`, definicional). **Verificado** con testigo
abierto:

```lean
example : Prf (provFromCode (substfc zero (tcFn #0) (formCode (add #0 zero =eq #0)))) :=
  pcc_ax4_inst (tcFn #0)          -- ✓ typechequea
```

### 19.4 Lo que queda de la evaluación provable

El caso **`σ` es gratis**: `ax_tc_succ` (`prf_tc_succ`) ya dice `tcFn (succ x) =eq succc (tcFn x)`.

Falta el caso **`+`** (y luego `lenc`/`nthc`/`carc`/`runFn`), enunciado internamente y probado por
**inducción interna** sobre el segundo sumando (`add` recurre por la derecha):

```text
⊢ ∀b.  Prov( ⌜ ȧ + ḃ  =  (a + b)˙ ⌝ )
```

- **Base** `b = 0`: instancia codificada de `ax4` (`pcc_ax4_inst`) + congruencia de `tcFn`.
- **Paso** `b → σb`: instancia codificada de `ax5` + `pcc_mp_code` + la HI + `prf_tc_succ`.
- La inducción es `prf_nat_induction` sobre la fórmula `provFromCode (…)` con `#0` libre; los lifts
  se empujan con **`liftFormula_provFromCode_open`**.

**No queda obstrucción conocida**: las reglas internas están todas disponibles y admiten testigos
abiertos, que era el bloqueo estructural.

---

## 20 · Primer paso REAL de la evaluación provable: `substfc` con testigo‑código arbitrario

**Hecho (2026‑07‑10), `Meta/SubstCodeOpenPrf.lean`.**

### 20.1 El hueco

`pcc_axiom_inst` (§19.3) entrega `provFromCode (substfc zero w (formCode φ))` con `w = tcFn a`. Para
**usarlo** hay que computar ese `substfc`. La única herramienta existente exigía que el código
sustituido fuese `termCode s` para una `s` **meta**:

```lean
prf_substFormula_arith (v s f) : substfc (numeral v) (termCode s) (formCode f) =eq formCode (substFormula v s f)
```

y `tcFn a` **no** es `termCode` de nada meta. Ese era el único hueco.

### 20.2 Por qué salió barato

En las pruebas originales `termCode s` viaja como argumento **opaco**: se pasa tal cual a
`prf_substtc_var_eq/gt/lt`, que están enunciadas para `s` **cualquiera** — son las «ecuaciones de
variable» de `substtc` que §11.3 señaló (y que `tcFn` no tiene). Sólo cambia el lado derecho.

### 20.3 Contenido

Funciones meta (código de `t`/`f` con el hueco de la variable `v` relleno por el **código** `w`):

```lean
mutual
  def substCodeT (v w) : Term → Term
    | .var n => if n = v then w else if n > v then varc ⌜n-1⌝ else varc ⌜n⌝   -- decremento De Bruijn
    | .func sym ts => funcc (strCode sym) (substCodeTs v w ts)
  def substCodeTs (v w) : List Term → Term
end
def substCodeF (v w) : Formula → Term      -- 8 casos, espejo de formCode
  | .forall a => ⟨6, substCodeF (v+1) (liftc zero w) a⟩   -- ¡el testigo se LEVANTA bajo el binder!
  | .ex a     => ⟨9, substCodeF (v+1) (liftc zero w) a⟩
  | …
```

Los dos lemas (misma estructura de casos que los originales, `[propext, choice, Quot.sound]`):

```lean
prf_substtc_arith_open (v w) : ∀ t, Prf (substtc ⌜v⌝ w ⌜t⌝ =eq substCodeT v w t)
prf_substtsc_arith_open (v w) : ∀ ts, …
prf_substfc_arith_open : ∀ v w f, Prf (substfc ⌜v⌝ w ⌜f⌝ =eq substCodeF v w f)
```

Chequeo de cordura (no duplicamos teoría): `substCodeT v (termCode s) t = termCode (substTerm v s t)`
(`substCodeT_termCode`), que recupera `prf_substTerm_arith`.

### 20.4 Confirmación De Bruijn

`prf_substfc_forall`/`_ex` dicen `substfc v t (forallc a) =eq forallc (substfc (σv) (liftc zero t) a)`:
al entrar bajo un binder el **testigo se levanta**. Es la confirmación *a posteriori* de por qué el
`∀`‑elim de código (§19.1) **debía** admitir testigos abiertos: aun instanciando un axioma cerrado,
el testigo interno acaba abierto.

### 20.5 Payoff verificado

```lean
-- la función meta COMPUTA (rfl):
substCodeF 0 w (add #0 zero =eq #0)  =  ⟨4, addcT w ⌜0⌝, w⟩

-- y la instancia de `ax4` CODIFICADO ya es usable:
Prf (provFromCode ⟨4, addcT (tcFn a) ⌜0⌝, tcFn a⟩)                       -- = Prov(⌜ȧ + 0 = ȧ⌝)
  := prf_mp (prf_provCode_congr (prf_substfc_arith_open 0 (tcFn a) _)) (pcc_ax4_inst (tcFn a))
```

### 20.6 Siguiente

1. **Cerrar la base de `+`**: de `Prov(⌜ȧ + 0 = ȧ⌝)` a `Prov(⌜ȧ + 0̇ = (a+0)˙⌝)` con `prf_tc_zero`
   (`tcFn zero =eq ⌜0⌝`) y `prf_congr_tcFn` sobre `ax4` object (`tcFn (add a zero) =eq tcFn a`),
   transportando con `prf_provCode_congr`.
2. **`pcc_axiom_inst2`** (axiomas `forall_2`, como `ax5`): `pcc_forallElim_code'` dos veces +
   `prf_substfc_forall`.
3. **Paso inductivo de `+`** y luego `lenc`/`nthc`/`carc`/`runFn`; después `<`, cuantificadores
   acotados, inducción estructural → `hbI`/`hbC` → `d3_prf` → `goedel_second_prf`.

---

*Fin del diseño. Estado 2026‑07‑09: `tcFn` (§10) descartado (§11.2); testigo‑lista naíf descartado
(§12.2); vía = **12‑A capa numérica Δ₀** (§12.4). **Fases 1 y 2 COMPLETAS** (`lenc`/`nthc` +
`prf_In_iff_boundedIn` + `prf_In_runFn_iff` + `prf_chainOk_iff_chainOkB`; el verificador ya es Δ₀ y
sin acumulador). **Fase 3 ARRANCADA** (§15: puente `d3_prf_of_reflect_bounded` — D3 reducida a
reflejar la forma acotada). Quedan el núcleo de fase 3 (reflexión atómica con `substfc`), fase 4
(cuantificadores acotados) y fase 5 (inducción estructural). Alternativa honesta siempre disponible
= Gödel II módulo axioma D3 (§11.4).*

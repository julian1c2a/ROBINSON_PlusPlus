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

```
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

> **DECISIÓN (2026‑07‑05): Opción A.** Análisis posterior confirma que el `∃`‑intro interno
> (`PrfH_pcc_exIntro`) produce **inherentemente** `formCode(A[0:=testigo])`; para el testigo
> abstracto eso reabsorbe la variable (`varc 0`), y la costura de B (`tcFn p =eq termCode p`) **no
> es enunciable** para `p` abstracto (`termCode p` meta‑stuck). Es una duda que **rompe la prueba
> entera**, no un detalle. Por el criterio «ante duda que pueda traer problemas → A», se adopta
> **Opción A**: rastreo uniforme desde la raíz (`provFormulaC'ₜ`/`provCodeC'ₜ` con `tcFn`/`substfc`)
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
   ```
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

*Fin del diseño. Ruta CONFIRMADA (2026‑07‑05c): la **Opción A `tcFn` (§10) queda descartada** para
el paso abstracto (§11.2); la vía genuina es la **Σ₁‑completitud provable estándar** (§11.3), cuyo
primer paso es fijar la codificación del testigo‑como‑número. Alternativa honesta siempre
disponible: consolidar Gödel II módulo el axioma D3 (§11.4).*

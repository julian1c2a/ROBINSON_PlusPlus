# Technical Reference — ROBINSON_PlusPlus

> ## ESTADO REAL — 2026-09-09 · rama A cerrada · **A5 y B8b cerradas** · C3: **5 de 7** reflectores · D3 a **DOS** obligaciones
>
> **Build 142 jobs · 0 errores · 0 warnings · 0 sorrys · Lean v4.31.0.**
> **128 módulos activos** (Minimal 11 + Meta 106 + Full 11) **+ 0 en `cuarentena/`** (fuera del build)
> **+ 61 en `sondeos/`** (experimentos compilados, fuera del build).
> **6 `axiom` de Lean** ([`AXIOMS.md`](AXIOMS.md)) · **141 axiomas objeto** en `axioms`.
>
> ### ✅ La inconsistencia conocida está REPARADA ([ADR‑012](DECISIONS.md))
>
> `ax_tc_cons` **retirado** de `axioms`: obligaba a `tcFn` a recurrir a la vez sobre estructura
> NUMERAL y sobre estructura de CÓDIGO — imposible, porque en ℕ el mismo valor es ambas cosas
> (`cons 0 nil = 2 = σσ0`). Los códigos de Gödel se escriben ahora como **NUMERALES**.
>
> * **`goedel_first_real'`, `godelC'_fixedpoint` y `goedel_first_undecidable_real'` YA NO EXISTEN.**
>   Gödel I es hoy **`goedel_first_numeral`** (`Meta/DiagonalNumeral.lean`), sobre `godelCN`.
> * **21 módulos a `cuarentena/`** ([ADR‑013](DECISIONS.md)) — cifra histórica del momento de la
>   reparación; hoy la cuarentena está **VACÍA** (§1.6). Sus teoremas eran formalmente correctos pero **vacuos**.
> * ⚠️ **NO es una prueba de consistencia**: se retiró la inconsistencia **conocida y localizada**.
>
> ### ✅ La ESCALERA (a.2) está COMPLETA — 4 de 4
>
> `pcc_eval_add` → `pcc_eval_mul` → `div2` → **`pcc_dot_cons`** (`Meta/DotConsPrf.lean`): la
> Σ₁‑completitud **internalizada** para argumentos abstractos, que es lo que repatría la cuarentena.
> Rédito verificado en `sondeos/CarcPayoff.lean` (`pcc_eval_carc` vuelve). Detalle en
> [Incompletitud §3.24–§3.32](doc/REFERENCE-Incompleteness.md).
>
> **Punto de reanudación:** **[NEXT-STEPS.md](NEXT-STEPS.md)** → **[PLAN-FRENTE-A.md](PLAN-FRENTE-A.md)**
> → [cuarentena/README.md](cuarentena/README.md) → [sondeos/README.md](sondeos/README.md).

**Last updated:** 2026-09-10d · Lean v4.31.0 — 🏁 **`hbody` PARTIDO** con la composición de los dos `substfc` (§3.59), y ⛔ **corregido**: la mitad (b) **sí** depende del análisis por tags (`premsOf` va por **21 axiomas**, uno por tag). ➕ La deuda del **testigo de `liftfc`**, enunciada y medida (§3.60). Antes: 🏁🏁 **D3 EN UNA SOLA OBLIGACIÓN** (§3.58): `hwP` probado en cuatro líneas ⇒ sólo queda **`hbody`**. Antes: 🏁 **`hPsiId` PROBADO** (§3.57): la **tercera variante** de la familia, nivel actuante **por debajo** del `substCodeF` ⇒ **D3 desde DOS obligaciones**. Antes: ⛔🏁 **D3 · §10: el `PsiF` del chasis** (§3.56): `hPl` era **FALSA** para el cuerpo de §8, y con el `PsiF` **dotado** caen **siete de las nueve** obligaciones de `pcc_bdAll_intro` ⇒ **D3 desde TRES**. Antes: 🏁🏁 **`pcc_eval_liftfc` PROBADO** (§3.53) ⇒ **q3 y qconf cerrados: CINCO de los SIETE** reflectores (§3.54); **D3 a DOS obligaciones** (§3.55); **dedup ADR‑019 de seis familias** (§3.52). Antes: 🏁 **A5 CERRADA** (`pcc_eval_liftc_at`/`_liftsc_at` con el nivel cuantificado, §3.50) y **B8b saldada** (el `prf_congr_liftc` duplicado no tenía consumidores, §3.51). Antes: **B3 EN CURSO**: `SubstfcPlanos` cerrado con DOS descensos (`binK`→`CodeCtorKit`, KIT TERNARIO→`EvalArithPrf`, que retira **74 copias**) + `Meta/SubstfcCodePrf.lean`; y la escalera `psi` subida a `StrongInductionPrf` (§3.35)

> **El historial detallado vive en [`CHANGELOG.md`](CHANGELOG.md)**, no aquí. Este índice describe
> el **estado actual**; la línea de "Last updated" dejó de ser un volcado acumulativo el
> 2026-08-22 (había crecido a ~20 KB en una sola línea, ilegible y sistemáticamente desfasada).

**Author**: Julián Calderón Almendros
**Lean version**: v4.31.0

---

## 0 · Naming Conventions Guide for the Reader

This project adopts [Mathlib](https://leanprover-community.github.io/contribute/naming.html)-style naming conventions. See `NAMING-CONVENTIONS.md` for the full reference and 12 formation rules.

### 0.1 Capitalization

- **Theorems/lemmas** (Prop): `snake_case` — `teo_2_7`, `mul_two_lt_mono`, `cantor_uniqueness`
- **Prop definitions** (predicates): `UpperCamelCase` — `IsFunction` (planned in Block7)
- **Functions/values**: `lowerCamelCase` — `pair`, `cantor_func`, `w_candidate`
- **Axioms**: `axNN_descriptor` or `ax_TagDescriptor` — `ax13_lt_def`, `ax_L0_cons_def`

### 0.2 Symbol-to-Word Dictionary

| Symbol | Name | | Symbol | Name | | Symbol | Name |
|--------|------|---|--------|------|---|--------|------|
| ∈ | `mem` / `In` | | + | `add` | | σ | `succ` |
| = | `eq` | | * | `mul` | | τ | `pred` |
| ≠ | `ne` | | − | `sub` | | √ | `sqrt` |
| ≤ | `le` | | / | `div` | | 0 | `zero` |
| < | `lt` | | ^ | `pow` | | 1 | `one` |
| ¬ | `not` / `neg` | | ∣ | `dvd` | | 2 | `two` |
| ⇔ | `iff` | | ↔ | `iff` | | ∅ | `empty` |
| ⇒ | `imp` (impl) | | ∨ | `lor` (or) | | ∧ | `land` (and) |

---

## 1 · Catálogo de módulos (índice raíz)

**El detalle exhaustivo (firmas Lean 4, dependencias por módulo, notación) vive en los nodos
temáticos `doc/REFERENCE-*.md`.** Esta tabla es el catálogo raíz; cada grupo enlaza a su nodo (árbol
REFERENCE, `AI-GUIDE.md` §0.5).

**128 módulos activos** (Minimal 11 + Meta 106 + Full 11) + barrel `Meta.lean` + raíz
`ROBINSON_PlusPlus.lean`. Fuera del build: **0 en `cuarentena/`** (§1.6) y **57 en `sondeos/`**
(experimentos compilados a mano; catálogo en [`sondeos/README.md`](sondeos/README.md)).

### 1.1 Núcleo → [`doc/REFERENCE-Kernel.md`](doc/REFERENCE-Kernel.md)

| Module | Namespace | Dependencies | Status |
|--------|-----------|--------------|--------|
| `Minimal/Axioms.lean` | `…Minimal.Axioms` | `FOL.FOL`, `FOL.Theorems.Eq` | ✅ Complete (Q++ + esquemas verificador + capa Δ₀ `lenc`/`nthc`/`ax_lineWF_inv`/`ax_lineWF_cons`) |

### 1.2 Aritmética desarrollada → [`doc/REFERENCE-Arithmetic.md`](doc/REFERENCE-Arithmetic.md)

| Module | Namespace | Dependencies | Status |
|--------|-----------|--------------|--------|
| `Minimal/Theorems/Block1.lean` | `…Block1` | `Axioms`, `FOL.Tactics` | ✅ Complete |
| `Minimal/Theorems/Block2.lean` | `…Block2` | `Axioms`, `Block1` | ✅ Complete |
| `Minimal/Theorems/Block3.lean` | `…Block3` | `Axioms`, `Block1`, `Block2` | ✅ Complete |
| `Minimal/Theorems/Block4.lean` | `…Block4` | `Axioms`, `Block1`, `Block3` | ✅ Complete |
| `Minimal/Theorems/Block4_C5.lean` | `…Block4_C5` | `Axioms`, `Block1`–`Block3` | ✅ Complete |
| `Minimal/Theorems/Block4_C6_C7.lean` | `…Block4_C6_C7` | `Axioms`, `Block1`–`Block4_C5` | ✅ Complete |
| `Minimal/Theorems/Block5.lean` | `…Block5` | `Axioms`, `Block1`–`Block4_C6_C7` | ✅ Complete |
| `Minimal/Theorems/Block6.lean` | `…Block6` | `Axioms`, `Block1`, `Block4`, `Block5` | ✅ Complete |
| `Minimal/Theorems/Block7.lean` | `…Block7` | `Axioms`, `Block1`, `Block4`, `Block4_C6_C7`, `Block5` | ✅ Complete |
| `Minimal/Theorems/Block8.lean` | `…Block8` | `Axioms`, `Block1`, `Block2`, `Block4_C5` | ✅ Complete (Fase 17 + Ax-P TFA) |

### 1.3 Gödelización Nivel B/C → [`doc/REFERENCE-Godelization.md`](doc/REFERENCE-Godelization.md)

| Module | Namespace | Dependencies | Status |
|--------|-----------|--------------|--------|
| `Meta/Godel.lean` | `…Meta.Godel` | `Axioms`, `Block6` | ✅ Nivel B: `G`, `⌜·⌝`, Teo G1 |
| `Meta/Provability.lean` | `…Meta.Provability` | `Axioms`, `Meta.Godel`, `FOL.*` | ✅ Nivel C: `formCode`, `IsFormula`, `Provable` (legacy retirada en F7a) |

### 1.4 Sistema `Full/` → [`doc/REFERENCE-Full.md`](doc/REFERENCE-Full.md)

| Module | Namespace | Dependencies | Status |
|--------|-----------|--------------|--------|
| `Full/Induction.lean` | `…Full` | `Axioms`, `FOL.*` | ✅ `ax_induction`/`inductionFormula` · 🆕 **ax6/7/10/11/12/18/19 empaquetados de verdad** (2026‑09‑10h: `add_assoc_thm`, `mul_assoc_thm`, `mul_distrib_thm` — la NOTA que declaraba imposible el `∀³` era FALSA). Censo completo en [REFERENCE-Full §3.14.1](doc/REFERENCE-Full.md). 🏁 **§0bis: `primAxioms`** (los 23 primitivos) + `primAxioms_subset` + `prim_to_axioms` + `axp` ([ADR‑023](DECISIONS.md)) — el andamio que **certifica** el censo, y ⭐ **no mueve la frontera de la teoría** (`axioms` intacta; `Derives.weakening` es constructor). 🏁 **2026‑09‑10h, RATIFICADO**: `axiom ax_induction_prim : primAxioms ⊢ inductionFormula φ`, y **`ax_induction` deja de ser `axiom`** (teorema por debilitamiento ⇒ siguen **6**). Con eso el módulo migra entero (35 declaraciones) y **ax6/7/10/11/12/18/19 quedan CERTIFICADOS** (`*_thm_prim`), con las firmas `axioms ⊢` de siempre re‑expuestas para los diez lemas que consumen otros módulos |
| `Full/Mod2.lean` | `…Full` | `Axioms`, `Block1`, `Full.Induction` | ✅ ax21/ax24 |
| `Full/Lists.lean` | `…Full` | `Axioms`, `Full.Induction` | ✅ `ax_list_induction` · 🏁 **ax_C3/ax_L3 CERTIFICADOS sobre `primAxioms`** ([ADR‑023](DECISIONS.md), 2026‑09‑10h): `concat_assoc_prim`/`in_concat_prim`, con **cero cambios de axioma** porque `ax_list_induction` ya era genérico en `Γ`. Las firmas `axioms ⊢` se conservan por `prim_to_axioms` |
| `Full/StrongInduction.lean` | `…Full` | `Axioms`, `Full.Induction` | ✅ inducción fuerte derivada |
| `Full/Numerals.lean` | `…Full` | `Axioms`, `Block1`, `Full.Induction` | ✅ puente `numeral` + homomorfismo |
| `Full/Bounded.lean` | `…Full` | `Axioms`, `Full.{Induction,StrongInduction,Numerals}` | ✅ `le_numeral_split` |
| `Full/Divisibility.lean` | `…Full` | `Axioms`, `Block1`, `Block8`, `Full.*` | ✅ `numeral_dvd`, `divisor_le` |
| `Full/Division.lean` | `…Full` | `Axioms`, `Full.Numerals` | ✅ `division_numeral` |
| `Full/PrimeFactor.lean` | `…Full` | (ℕ pura) | ✅ Euclides + unicidad |
| `Full/Primality.lean` | `…Full` | `Axioms`, `Block1`, `Block8`, `Full.*` | ✅ `isPrime_numeral` |
| `Full/Factorization.lean` | `…Full` | `Axioms`, `Block8`, `Full.{Numerals,PrimeFactor}` | ✅ **`tfa_numeral`** (TFA completo) |

### 1.5 Incompletitud Nivel D → [`doc/REFERENCE-Incompleteness.md`](doc/REFERENCE-Incompleteness.md)

Los **88 módulos** de `Meta/`, en el orden del barrel [`Meta.lean`](ROBINSON_PlusPlus/Meta.lean).
Detalle en el nodo §3.15–§3.32.

| # | Module | Rol · Estado |
|--:|--------|--------------|
| 1–2 | `Godel.lean` · `Provability.lean` | Nivel B/C — ver §1.3 |
| 3–5 | `Hilbert.lean` · `HilbertDeduction.lean` · `HilbertSeq.lean` | F0/F1: `Prf₀`/`Prf` + puentes (`dne` aislado); deducción finitaria `PrfH`; `checkProof`, `Dem`, `dem_tracks` |
| 6–9 | `CodeArith.lean` · `SubstArith.lean` · `StepArith.lean` · `CheckArith.lean` | F2.1–2.4: aritmética de códigos, sustitución/lift De Bruijn, `validProofFn` (19 reglas) + `provCodeC` Σ₁ |
| 10–12 | `Representability.lean` · `Necessitation.lean` · `Diagonal.lean` | F2.5–F3: `repr_pos`, D1/`necessitation`, `diag_arith`, `tc_numeral` |
| 13–15 | `CodeDistinct.lean` · `Induction.lean` · `ListInductionArith.lean` | aritmética negativa `formCode_ne`/`strCode_ne`; reglas `ind`/`listInd` (IΣ₁) |
| 16 | `ProofChain.lean` | verificador estructural `runFn`/`chainOk`/`lineOk`/`allIn` + `provCodeC'` |
| 17–19 | `DerivCond.lean` · `Representability2.lean` · `Reflection.lean` | **D2** `d2`, **D1** `repr_pos'`, combinadores (capa ω) |
| 20–26 | `ReprPrf` · `LineWFDerives` · `ArithPrf` · `Representability2Prf` · `ChainPrf` · `DerivCondPrf` · `ReflectionPrf` | re‑nivelación HBL a `Prf`: **D1** `repr_pos'_prf` ✅, **D2** `d2_prf` ✅, **D3 reducida** `d3_prf_of_sigma1` |
| 27–29 | `Sigma1Prf` · `TcArithPrf` · `NumListPrf` | reflexión Σ₁; `tcFn` (`prf_tc_zero`/`_succ`/**`prf_tc_numeral`**); `lenc`/`nthc` |
| 30–34 | `NatArithPrf` · `NatOrderPrf` · `NatMulPrf` · `CantorMonoPrf` · `Div2ParityPrf` | **aritmética en `Prf`**: `<` y `prf_nat_induction`; orden `≤`; producto y cancelación; **`prf_cantor_mono_left/right`**; **`prf_div2_numeral`**, **`prf_cons_double`** (§3.24.3–4) |
| 35–36 | **`CodeNumeralPrf`** · **`DiagonalNumeral`** | **LA REPARACIÓN (ADR‑012)**: `consN` por números triangulares, `codeNat`, **`prf_formCode_numeral`**; lema diagonal numeral, **`goedel_first_numeral`** (Gödel I) (§3.24.2/§3.24.5) |
| 37 | `Sigma1CorePrf` | **keystone de (a.1)**, refundado a códigos numerales (§3.24.7) |
| 38–39 | **`EvalArithPrf`** · **`EvalMulPrf`** | **escalera (a.2) 1–2**: `pcc_eval_add`, `pcc_eval_mul`; toolkit ecuacional interno (§3.25.1–2) |
| 40–47 | `ExIntroCodePrf` · `ForallElimCodePrf` · `LineWFCases` · `MpCodePrf` · `OmegaReflect` · `Sigma1AtomPrf` · `Sigma1TrackedPrf` · `TrackedCorePrf` | sistema interno a nivel de código (`pcc_axiom_inst`, **`pcc_thm_inst`**); los 21 tags; `Reflects`/`reflects_of_omega`/`NegVerifier`; átomo `=eq`; testigo rastreado. 🆕 **`OmegaReflect` 2026‑09‑10h ([ADR‑022](DECISIONS.md))**: la clase de testigos **se estrecha** de `IsCodeShaped` a **`StdLine`** (`⟨⌜f⌝, k̄, args⟩` con args `formCode`/`termCode`). ⛔ Motivo medido: el docstring viejo afirmaba que las comparaciones son «paralelas por tipo, nunca `cons` contra `numeral`» y **era FALSO sobre su propia clase** (`sondeos/MedirF_Censo.lean` §4) ⇒ la refutación exigía **evaluar Cantor**, inviable. 🏁 La garantía que lo hace admisible: **`stdChain_proofCode'`** — la clase contiene los códigos de prueba **reales**, los 21 tags. ⚠️ Precio escrito: `OmegaConsistent` es **estrictamente más fuerte** |
| 48 | `StrongInductionPrf` | **inducción fuerte en `Prf`**, net‑0 y en forma OBJETO (`prf_strong_induction`) (§3.24.6). Más la **escalera `psi`** genérica en `Φ`: `psi_lift_form`‑`4` y `PSI_inst`/`2`/`3`/`4`, un escalón por cada número de binders sobre `Φ`. ⚠️ **`PSI_inst2` faltaba** hasta A5 (2026‑09‑09c, §3.50.4): estaban el 1, el 3 y el 4 porque ningún frente había inducido con exactamente DOS binders |
| 49–52 | `BoundedInPrf` · `RunFnBoundedPrf` · `ChainOkBoundedPrf` · `Sigma1BoundedPrf` | 12‑A fases 1‑3: capa Δ₀ del verificador + `d3_prf_of_reflect_bounded` |
| 53–54 | `SubstCodeOpenPrf` · `NumCodeClosedPrf` | `prf_substfc_arith_open`, `substCodeT_closed`; `prf_liftc_tcFn`, `prf_substtc_tcFn`. 🏁 **2026‑09‑09g‑h**: el **ladrillo de nivel TÉRMINO** de `hPinv` (`substtc_inv_substCodeT` y su variante `_at`). ⚠️ **NO es `hPinv`** — ése es de nivel FÓRMULA y vive en `BdAllIntroPrf`; aquí no cabe (aguas arriba de `atomc`/`eqCodeFn`). El docstring original **sobreclamaba** y está corregido. 🏁 **2026‑09‑10 (§3.57)**: §5 añade la **TERCERA variante**, `substtc_id_substCodeT`/`_Ts` —nivel actuante **por debajo** del código—, más **`prf_liftc_varc_numeral`** (`liftc 0 ⌜v_k⌝ ≐ ⌜v_{k+1}⌝`, genérico en el nivel), que **absorbe** el `prf_liftc_varc0` de `TrackedAtomsPrf` (ADR‑019: pasa a ser su instancia). ⚠️ Por debajo el **testigo deja de ser libre** (`u ≐ varc v̄`) y el índice **no admite salto**: a `v+2` o más el enunciado sería **falso** |
| 55 | **`DotConsPrf`** | **escalera (a.2) peldaño 4 — `pcc_dot_cons`** ✅, más **`pcc_rw`** / **`pcc_rw_imp`** / `pcc_rw_div2` (§3.25.3) |
| 56–60 | **`EvalListPrf`** · `EvalLtPrf` · `EvalRunFnPrf` · `EvalBoundedPrf` · **`EvalNthcPrf`** | 🔁 **repatriados**: evaluación provable de `carc`/`cdrc`/`lenc`, `<`, `∃i<B`/`∀i<B`, `nthc`. Moldes **`pcc_rw_dot_cons_un`** y **`pcc_rw_dot_cons_nthc`** (§3.26) |
| 61–64 | `Delta0ReflectPrf` · **`D3DottedPrf`** · `PropCodePrf` · `EvalCarcNthcPrf` | 🔁 reflexión Δ₀; **`d3_prf_of_dotted_atoms`** (net‑0); §39 lógica interna (`pcc_ind_code`); `carc∘nthc` |
| 65–66 | **`D3InDotPrf`** · `BdAllIntroPrf` | 🔁 **`hI_dot`** y **`d3_prf_of_chainOkDot`** (D3 ⇐ `hC_dot` SOLO); **`prf_tc_form_numeral`** + **`pcc_to_formCode`** (§3.26.2); §40 `pcc_bdAll_intro`. 🏁 **2026‑09‑09h**: entra el **`hPinv` GENÉRICO a nivel FÓRMULA** (`substfc_inv_substCodeF` y `substfc_inv_substCodeF_at`), que hasta hoy se pagaba **a mano en cada frente**. ⭐ La clave, y lo que una medición anterior dio por imposible: **las dos hipótesis son cerradas bajo `liftc 0`** (`substCode_hyps_lift`, 3 líneas) ⇒ la inducción atraviesa los binders. ⚠️ Hacen falta **las dos variantes**: el ÍNDICE cambia la condición sobre variables libres. 🏁 **2026‑09‑10 (§3.57)**: y una **TERCERA**, `substfc_id_substCodeF` —la que consume **`hPsiId`**—, con el nivel actuante **por debajo** del `substCodeF` y el **testigo ATADO** (`u ≐ varc v̄`). 📖 Va como **parámetro con su ecuación**, no clavado con `prf_congr_substfc_arg2`: es la regla de §3.50 —*parametriza por los dos niveles*— porque bajo el binder aparece `liftc 0 u`, que no es sintácticamente la variable de arriba |
| 67–69 | **`LineWFTrackedPrf`** · `LineWFMpPrf` · `LineWFSchemaPrf` | 🔁 reflexión punteada de `lineWF`; **`pcc_dot_eqc`**; chasis `pcc_lineWF_tracked_of_schema` |
| 70–73 | **`CodeCtorKit`** · `LineWFEfqPrf` · **`CodeTreeReflect`** · `LineWFPropPrf` | 🔁 **el KIT**: `pcc_dot_nul`/`_un`/`_bin` (+ simétricas) y sus congruencias internas; **`pcc_tc_objAt`** (recursión sobre `CTree` dentro de `Prov`) (§3.26.3) |
| 74 | **`EvalPredPrf`** | 🆕 **la evaluación DOTADA de `pred`** (2026‑08‑31, promovido de `sondeos/EvalPredDot.lean`): `pcc_eval_pred (n)` con `n` **ABSTRACTO**, más `pcc_eval_varc_pred`. Lo pide `ax_substtc_var_gt`, cuya cláusula devuelve `varc (pred n)`. ⚠️ `predcT` es **DEFINICIÓN**: no se postula ninguna ecuación de recursión suya (§3.30) |
| 75 | **`CodeWitnessPrf`** | 🆕 **el vocabulario de TESTIGOS del frente `substfc`** (2026‑08‑31, promovido de `sondeos/HasWitFRealMin.lean`). Tres bloques: `SinWTs` (reconocedor de TÉRMINO con una lista, `isTC1`/`wfAll1`/`argsIn`, más `isFormCodeB2`), `ENS` (reconocedor de FÓRMULA **ecuacional** con dos listas, `isFC1`/`hasWitF`) y `HW` (**la NO‑VACUIDAD**: `prf_hasWitF_real`, net‑0 **puro**). ⚠️ Se **dedupliparon nueve** definiciones al promover (§3.31). 🏁 **B8b saldada** (2026‑09‑09c, §3.51): se borra su `prf_congr_liftc` — duplicado del de `NumCodeClosedPrf` con el nivel explícito en vez de implícito — porque la medición dio **cero consumidores** en todo el árbol; estaba en el `export` por EXISTENCIA, no por consumo (§17) |
| 76 | **`CodeNatInjPrf`** | 🆕 **inyectividad de la codificación numeral** (2026‑09‑01, promovido de `sondeos/CodeNatInj.lean`): `consN_inj` (Cantor) → `codeNat_inj` → **`codeNat_ne`/`codeNatTerm_ne`**, el **sustituto de `canon_ne`** que desbloquea los casos 3‑4 del módulo C de `NegVerifier`. ⚠️ Trae también `num_bridge`, el puente entre los **dos `numeral`** duplicados del proyecto |
| 77 | **`LiftcCodePrf`** | 🆕 **los constructores de código DOTADOS y las cláusulas del reflector** (2026‑09‑03, promovido de `sondeos/ReflectorDesdeConsumidor.lean`): `liftcT`/`liftscT`/`varcT`/`funccT` con sus puentes `rfl`, las congruencias META e INTERNAS, `targetLift`/`targetLiftsc`, las cuatro ecuaciones dotadas de `liftc`/`liftsc` y las cuatro cláusulas del reflector en **moneda de inducción OBJETO**. ⚠️ Se **descartaron DIEZ duplicados** al promover (§3.33). 🏁 **A5** (2026‑09‑09c, §3.50): §7bis y §9bis repiten las cuatro cláusulas **a NIVEL ARBITRARIO** (`refl_caso_varc_at`, `refl_caso_funcc_at`, `refl_lista_nil_at`, `refl_lista_cons_at` y sus cuatro `_imp_at`), con `targetLiftAt`/`targetLiftscAt`, sus huecos y `PrfH_congr_targetLiftAt`/`_targetLiftscAt`. ⭐ Sale barato porque **en el sorte TÉRMINO el nivel es INERTE** y las reflexiones internas de §4 ya eran genéricas en él; lo único nuevo es el `varc`, donde aparece la **tricotomía** — de ahí `pcc_liftc_var_lt_code` (la mitad de `ax_liftc_var_lt` que no estaba dotada) y `prf_liftc_varc_cases`. ➕ **2026‑09‑09i**: `substTerm_formCode` —el gemelo del `liftTerm_formCode` de `DerivCondPrf`, que **no existía**—. ⚠️ Vive aquí **por dependencia, no por tema** (necesita `substTerm_termCode`/`_termsCode`, y `DerivCondPrf` está aguas arriba); lo consume `D3ChainDotPrf` §10 |
| 77b | **`EvalLiftcPrf`** | 🆕 **EL DESCENSO** (2026‑09‑04, promovido de `sondeos/DescensoLiftc.lean`, rama **B2**): la inducción fuerte que cierra **`pcc_eval_liftc`** — el `hLift` que `Paso2CasoForall` dejaba sin descargar — más `DESCENSO_hasWit`, la forma consumible contra `ENS.hasWit`. 🔑 **UNA** inducción fuerte con conclusión **CONJUNTIVA** sobre los dos sorts y `w` cuantificado **DENTRO** de `Φ`; `PHI_step` consume las cláusulas `_imp`, o sea la **moneda OBJETO**. De 198 declaraciones del sondeo se promovieron **31**; ⚠️ **seis piezas genéricas se subieron aguas ARRIBA** (a `StrongInductionPrf` y a `SinWTs`) y **dos BAJARON** a `LiftcCodePrf` — ver §3.34. `export` **PARCIAL a propósito**: `PHI*`/`DESCENSO*` quedan cualificados porque `EvalSubstfcPrf` monta otros dos descensos con los mismos nombres. 🏁 **A5** (2026‑09‑09c, §3.50.4): §7bis repite el descenso con el **NIVEL cuantificado dentro de `Φ`** (`Φat(X) := ∀c.∀w. …`) — el nivel entra en `Φ` por la MISMA razón que `w`, el gate `liftFormula 1 Φ = Φ` — y produce **`pcc_eval_liftc_at`** y **`pcc_eval_liftsc_at`**, el prerrequisito que §3.49.1 había medido para `pcc_eval_liftfc` (⬜ aún NO existe: es la deuda enunciada en `EvalLiftfcPrf`). ⚠️ La recursión es la MISMA (Cantor sobre `carc`/`cdrc`): `c` viaja intacto |
| 77c | **`SubstfcCodePrf`** | 🆕 **el caso BINARIO y el caso BOTTOM de `substfc`** (2026‑09‑04, promovido de `sondeos/SubstfcPlanos.lean`, rama **B3**): `binct` con la ETIQUETA abstracta —que hace `implc`/`andc`/`orc` en UN lema en vez de tres—, los cuerpos `AXBIN_BODY`/`AXBOT_BODY`, `evalSubstfcCode` y las instancias dotadas `pcc_substfc_bin_dot`/`_bottom_dot`. De las 39 del sondeo aquí viven **17**: 18 ya estaban (13 por los dos DESCENSOS de esta rama, a `CodeCtorKit` y `EvalArithPrf`) y ⚠️ **4 se retiran por MUERTAS** — `paso2_caso_bin`/`_impl`/`_and`/`_or` no tienen ni un consumidor de código: el ensamblaje real usa `paso2_caso_bin_imp`, el mismo caso en **moneda OBJETO**, porque en la inducción la HI llega como hipótesis |
| 77d | **`HasWitTcFnPrf`** | 🆕 **`∀t. hasWit (tcFn t)`** (2026‑09‑05, promovido de `sondeos/HasWitTcFn.lean`, rama **C** / [ADR‑020](DECISIONS.md)): la buena formación de los códigos **PUNTEADOS**, por **inducción OBJETO** — la única ruta posible, porque `tcFn` es un átomo opaco con sólo `ax_tc_zero`/`ax_tc_succ` vivos. Footprint `[propext, Classical.choice, Quot.sound]`, **net‑0 puro** (la inducción entra por `Prf.ind`, no por `ax_induction`). 🔑 Aporta además **tres piezas GENÉRICAS** que no existían — `prf_argsIn_mono`, `prf_isTermCodeE1_mono`, `prf_wfAll1_cons` (monotonía y extensión de testigo) —, válidas también para el lado `hasWitF` |
| 77e | **`SubstfcWitnessPrf`** | 🆕 🏁 **LAS DOS CLAUSURAS de las guardas bajo la sustitución OBJETO** (2026‑09‑06, promovido de `sondeos/ClausuraSubsttc.lean`, rama **C** / [ADR‑020](DECISIONS.md)): `prf_hasWit_substtc (v s t)` y ⭐ **`prf_hasWitF_substfc (v s X)`** — *la pieza que §3.36.5 identificó como lo único que separaba el árbol del verde*—, las dos con el código y el sustituyendo **ABSTRACTOS**. Footprint `[propext, Classical.choice, Quot.sound]`, **net‑0 puro**. 🔑 Método (§3.38.1): **sacar el `∃` fuera *también de la maquinaria*** —toda la fusión de testigos se prueba con testigos abstractos y en implicación OBJETO, así que no hay ni un índice De Bruijn que mover— y **cada caso genérico en el contexto**, con sus hipótesis por argumento, que es lo que hace manejables los **siete `or`‑elim anidados** de `isFormCodeE2`. La mitad FÓRMULA **no es conjuntiva**: `bot`/`atom`/`eq` **no inducen**. ⚠️ Al promover: `psi_lift_form4`/`PSI_inst4` subieron a `StrongInductionPrf`, `PrfH_congr_substfc3` bajó a `NumCodeClosedPrf` desde `BdAllIntroPrf`, y la familia `nilOrCons`/`prf_nil_or_cons` bajó desde `EvalLiftcPrf` (ADR‑019, tres veces) |
| 77f | **`EvalSubsttcPrf`** | 🆕 🏁 **LA EVALUACIÓN PROVABLE de `substtc`/`substtsc`** (2026‑09‑07, promovido de `sondeos/EvalSubsttc.lean`, rama **B3.2**): `pcc_eval_substtc (w v s t)` con `v`,`s`,`t` **ABSTRACTOS** y el testigo `w` como guarda, su gemela sobre listas `pcc_eval_substtsc`, y `pcc_eval_substtc_hasWit` con el testigo cuantificado. Molde de `EvalLiftcPrf`: UNA inducción fuerte con conclusión CONJUNTIVA sobre los dos sorts y tres binders dentro de `Φ`. Footprint = la base sancionada; **ni un axioma nuevo**. ⚠️ **La promoción fue sobre todo BORRADO**: de 154 declaraciones entraron **71** — 66 duplicados exactos, 4 **instancias** de genéricos ya subidos (`psi_lift_form3`/`PSI_inst3`), 3 muertas, y ⭐ **el §13 entero**, ocho declaraciones para descargar una hipótesis `PredHyp` que producción ya probaba **sin guarda** (`pcc_eval_pred'`): queda en tres líneas. ⛔ **13 nombres RENOMBRADOS antes de mover** (homónimos de `EvalLiftcPrf`/`LiftcCodePrf`), y dos de ellos —`PHI`/`PHIbody`— con la **misma firma y distinto cuerpo**: ningún comparador de enunciados los separa |
| 77g | **`LineWFGuardPrf`** | 🆕 **EL CHASIS del conjunto extra de [ADR‑020](DECISIONS.md)** (2026‑09‑07): `hcond_absorbe_extra` —el lema sobre el que se aceptó la ADR, que vivía en **cinco copias fuera del build**— y ⭐ **`hcond_absorbe_cascade`**, que absorbe la cascada entera por inducción sobre la lista de casillas y **reduce la deuda de los 7 tags a DOS lemas genéricos**, `DEUDA_hGuardT`/`DEUDA_hGuardF`, **enunciados y no postulados** (cero `axiom`). Footprint `[propext, Classical.choice, Quot.sound]`, **net‑0 puro**. ⚠️ La forma real de la enmienda es una **cascada anidada a la derecha** de 1–3 guardas por tag (7 `hasWitF` + 4 `hasWit` = los 11 conjuntos de la ADR), **no** un par: §2.1 lo **comprueba con siete `rfl`** contra `Minimal/Axioms.lean`, y ese `rfl` cazó tres tags mal supuestos. **No prueba las dos deudas** (falta el recorrido de `isTC1`/`isFC1` bajo el `∃`) — 🏁🏁 **pero ya están las dos probadas** (`pcc_hGuardT` 2026‑09‑08c, `pcc_hGuardF` 2026‑09‑08e; filas 84d y 84e), y con `hGuard_of_slots` **la cascada no tiene ninguna obligación abierta**. 🆕 **2026‑09‑08f · §5**: los absorbedores **dependientes** `hcond_absorbe_1/2/3`, que dan al núcleo estructural la fórmula guardada **entera** — sin ellos `pcc_eval_substfc_wit` (cuyo antecedente OBJETO **son** las guardas) no se puede pagar, y `hCarc` no es una MP |
| 77h | **`EvalSubstfcPrf`** | 🆕 🏁 ⭐ **EL MURO DE `substfc`, EN PRODUCCIÓN** (2026‑09‑08, promovido de `sondeos/EvalSubstfcPrf.lean`, rama **B3.4**): **`pcc_eval_substfc (wF wT v s f)`** con `v`,`s`,`f` **abstractos** y los testigos como guarda, y **`pcc_eval_substfc_wit (v s f) : Prf (hasWit s ∧ hasWitF f ⇒ targetSubstfc v s f)`** — cuyo antecedente es **literalmente** el conjunto extra de [ADR‑020](DECISIONS.md), así que con él `hCarc` pasa a ser una MP (ver `LineWFGuardPrf`). Más el **chasis genérico** `pcc_eval_substfc_modulo_8`, parametrizado sobre los ocho casos. Footprint = la base sancionada; `pcc_congr_substfcT_arg2_code`, **net‑0 puro**. 🔑 **No hacen falta tres sorts**: la inducción de fórmula es de **UN SOLO SORT** y consume término/lista como caja negra, vía `pcc_eval_substtc`/`_substtsc` (B3.2). 🔑 **El puente de testigos se DISUELVE**: `isFormCodeE2` tiene las casillas de término apuntando a `wT` en la forma exacta que consume `EvalSubsttcPrf` ⇒ la premisa sale por `rfl`. ⚠️ **De 806 declaraciones entran 90**: el sondeo era la **acreción de CINCO sondeos** (cuatro namespaces copiaban trabajo ya promovido) y `ENS` sólo dependía de **41** nombres de ellos, **31 ya en producción**. Los **16 lemas puente `bridge_*`** se disuelven (cero usos: eran certificados de que dos namespaces definían lo mismo). ⛔ Y una clase NUEVA de duplicado falso: `hPHI` tiene la misma **firma** que el de `EvalLiftcPrf`, pero la firma menciona `PHI`, que es un **homónimo** |
| 78–80 | **`InAxiomsCodePrf`** · `LineWFThyPrf` · `LineWFAssemblePrf` | 🔁 `pcc_In_axiomsCodeT_tracked`, **`pcc_tc_formCode_internal`**; **`pcc_lineWF_tracked_modulo_7`** (§3.26.4) |
| 81–82 | `LineWFConsPrf` · `AxiomListCode` | `prf_line_is_cons`; `axiomsCodeT` concretado (`neg_In_axiomsCodeT`) |
| 83–84 | `CodeDecode` · `ChainDecode` | **módulo A de `NegVerifier`**: `decodeForm` biyección + `decodeChain_prf` |
| 84c | **`TrackedAtomsPrf`** | 🆕 ⭐ **EL KIT GENÉRICO de reflexión Σ₁ con argumentos ABSTRACTOS** (2026‑09‑08, promovido de `sondeos/A3IsFCBTracked.lean`, 21 de 81 declaraciones, **cero homónimos**): **`pcc_In_atom_tracked (x w)`** —el átomo `In` reflejado con los dos argumentos abstractos, que es lo que permite partir la guarda de ADR‑020—, `pcc_boundedIn_tracked`, `pcc_shape_tracked`, `pcc_child_tracked`, ⭐ **`pcc_child_tracked_at`** (índice **abstracto**: el cuerpo que pide un `∀` acotado ANIDADO), `pcc_carcIn_tracked`/`_cdrcIn_tracked`. Sirve a **C3‑T**, **C3‑F** y **D3** a la vez, porque es la mitad del trabajo que **no depende del predicado de nodo**. De 14 errores a 0: diez guardas de ADR‑020 se **pagan** con `hw_auto`; la undécima (`PrfH_in_transport`, tres argumentos abstractos) **no se puede pagar** y se **arrastra** con `autoParam`. ⚠️ Aquel sondeo metió el `In` como **átomo a propósito**, para que el cuerpo del `∀` acotado no tuviera binders — `isTermCodeE1` **no** tiene esa propiedad ⭐ **2026‑09‑08c — `pcc_shape_tree`**: una forma posicional (`shapeUn`/`shapeBin`) reflejada **directamente a su código `formCode`**, no a `shapeDot`. Genérica en el `CTree`, luego reutilizable por C3‑F y D3. Se compone de dos piezas que `Meta/CodeTreeReflect.lean` ya tenía probadas por inducción (`pcc_tc_objAt`, `PrfH_dotVN`), así que **no hizo falta ningún teorema objeto nuevo**. Con ella, `prf_substfc_shapeDot_at` (nivel arbitrario). |
| 84d | **`HasWitTrackedPrf`** | 🆕 **`DEUDA_hGuardT` baja a UNA obligación de contenido** (2026‑09‑08): `pcc_isTC1_tracked_of`, la plantilla `isFCB` de A3 portada a `isTC1 w c = wfAll1 w ∧ In c w` — cuatro líneas sobre el kit, con la mitad derecha pagada por `pcc_In_atom_tracked`. Genérico en la imagen punteada `WD`, para no prejuzgar la que salga del `pcc_bdAll_intro`. §1 comprueba la forma contra `Minimal/Axioms.lean` con dos `rfl`. ⭐ **§4: el `∀` acotado ANIDADO de `argsIn`, REFLEJADO** (`pcc_argsIn_pair_tracked`) — **sin reformular `isTermCodeE1`**, o sea sin tocar `Minimal/Axioms.lean` ni los 7 axiomas de ADR‑020. 🔑 `pcc_bdAll_intro` es META‑nivel (cuantifica `q`,`i` en Lean), luego anidar dos `∀` en la FÓRMULA son dos aplicaciones independientes. ⚠️ La fricción real era otra: `CF` ha de ser natural en UN parámetro y `argsIn wT Y` tiene dos libres ⇒ empaquetar con `cons` y leer con `carc`/`cdrc`. De `DEUDA_wfAll1_tracked` queda el recorrido de los dos disyuntos y el `pcc_bdAll_intro` exterior 🏁 **2026‑09‑08c · `DEUDA_hGuardT` PROBADA** (`pcc_hGuardT (i n t) (hin : i < n)`), y con ella `hGuard_of_deudaF`: la cascada de ADR‑020 con la mitad `wit` descargada — queda sólo `DEUDA_hGuardF`. ⚠️ **La corrección que mandó el frente**: `condD C t = substfc 0 ṫ (formCode C)` **no admite elegir imagen**, y la de `formCode (shapeUn X k)` es la ECUACIÓN POSICIONAL, no `shapeDot`; §5‑§9 se rehicieron sobre `shapeFCun`/`shapeFCbin`, casados con `formCode` por `rfl`. ⭐ §10 `pcc_wfAll1_trackedC` (la cota, de `(lenc w)˙` a `lencT ẇ`, dentro de `Prov`); §11 el paso `∃` (`pcc_hasWit_exc`), con el testigo como **variable de código que se desplaza** `⌜v₀⌝`→`⌜v₁⌝`→`⌜v₂⌝` ⇒ **dos** ranuras de testigo en `wfAll1PsiAtC`; §12 la alineación con `condD`, que sale por **`rfl`** (`prf_substfc_arith_open` + `substCodeF`). ⚠️ La cota `i < n` **no es artefacto**: `pcc_eval_nthc` la exige; las cuatro casillas reales la cumplen. |
| 84e | **`HasWitFTrackedPrf`** | 🆕 **C3‑F: la mitad cara de `DEUDA_hGuardF`, probada** (2026‑09‑08d, 828 l., net‑0 puro): **`pcc_wfAllF_trackedC (wF wT)`** — `wfAllF` reflejado con los **dos** testigos abstractos y la cota ya dotada — sobre **`pcc_isFormCodeE2_trackedC`**, el recorrido de las **ocho** cláusulas. ⭐ Lo primero del módulo son **siete `example … := rfl`** que casan la imagen con la que `substCodeF` produce (la regla de §3.44 aplicada **antes** de construir: acertaron todos a la primera). Trae la **tercera** forma posicional (`pcc_shapeNul_fc`, vía `CTree.nul`) y tres factorizaciones que evitan multiplicar por ocho: `clEq = clBin · 4` **por `rfl`** (cuatro lemas, no ocho), **`PrfH_clIn`** (el átomo `In (nthc X ȷ̇) w` transportado, que aparece **diez** veces) y **`prf_or_imp_of`** (`pcc_reflect_or` **arrastrando** la ecuación del nodo, que la deuda B6b obliga a llevar como antecedente objeto). Confirma que `pcc_shape_tree` era genérica en el árbol y `shapeFCun`/`shapeFCbin` en el tag. ⬜ Queda `isFC1`, el `∃∃` (dos `pcc_exIntro_code_open`, que piden el descenso a nivel arbitrario) y la fontanería `condD` 🏁🏁 **2026‑09‑08e · `DEUDA_hGuardF` PROBADA** (`pcc_hGuardF`, 1 230 l., net‑0 puro), y con `hGuard_of_slots` **la cascada de ADR‑020 queda sin ninguna obligación abierta**. El trabajo estaba entero en el **`∃∃`**: el `∃` EXTERIOR liga `wF` y el INTERIOR `wT`, así que los huecos se rellenan **en dos pasadas y a NIVELES DISTINTOS** ⇒ hubo que **abrir el nivel** de la keystone (`prf_substfc_wfAll1DotAtC_gen`, del que el lema de C3‑T pasa a ser la instancia `v = 0`) y escribir su gemelo `prf_substfc_wfAllFDotAtC_gen`; los dos `pcc_exIntro_code_open` se encadenan por `prf_substfc_ex`. La alineación con `condD`, otra vez por `rfl`. ⚠️ **No cierra C3**: `pcc_lineWF_tracked_modulo_7` sigue pidiendo los 7 reflectores de sustitución (hay 14 en el árbol y ninguno de esos siete) — pero lo que les falta es ya sólo la condición **estructural**, que es lo que B3.2/B3.4 compraron. |
| 84f | **`SubstTreeReflect`** | 🆕 **C3 · el chasis del árbol de código CON nodos `substfc`** (2026‑09‑08f). `STree` espeja `CTree` añadiendo `sub s f` (= `substfc 0 s f`), con sus cinco inducciones puras y `prf_condD_of_stree_eq`. ⛔ **Tipo nuevo y no extensión de `CTree` por CICLO DE IMPORTS**: el paso caro del nodo `sub` es `pcc_eval_substfc` (B3.4) y `CodeTreeReflect` está aguas arriba de ese módulo. ⭐ Declara `treeQ1`/`treeQ2`/`treeLeibniz` y los casa **por `rfl` con `ax_lineWF_q1`/`_q2`/`_leibniz` ENTEROS, cascada de guardas incluida** — con lo que el `∃ C` de §2.1 de `LineWFGuardPrf` queda resuelto para tres tags. Footprint: **sólo los tres axiomas de Lean**. ⬜ Falta `PrfH_dotVN` para `STree`, cuyo único caso nuevo es `sub` 🏁 **2026‑09‑09 · TRES de los SIETE reflectores, PROBADOS**: `pcc_lineWF_tracked_q1_imp` (tag 9), `_q2_imp` (10) y `_leibniz_imp` (13), net‑0 puros. Piezas: `SGuards` (las guardas **sólo** en los nodos `sub`), `PrfH_tc_objAt` (el «código del código», donde `pcc_eval_substfc_wit` cobra las guardas), `PrfH_dotVN` (pura congruencia), `pcc_condDS_of_stree` y `pcc_lineWF_tracked_of_stree`. ⭐ **Las guardas de ADR‑020 son exactamente los hijos del nodo `sub`**: la `witF` sobre el cuerpo del `substfc`, la `wit` sobre el sustituyendo — la forma de la enmienda resulta ser la aridad de los nodos `sub`. ⚠️ Corrige §3.47.5: `dotVN` **no** paga la guarda, la paga `tc_objAt`. 🏁 **2026‑09‑09e (§3.54): q3 (11) y qconf (19) ⇒ CINCO de los SIETE.** `STree` gana el nodo **`lift n a`**; su caso en `PrfH_tc_objAt` es el **análogo unario del `sub`** (un hijo, una guarda, `pcc_eval_liftfc_wit`) y en `PrfH_dotVN` es pura congruencia. ⭐⭐ Y **la guarda de ADR‑020 vuelve a caer exactamente sobre el hijo del nodo** — el mismo hallazgo que con `sub`, en un frente independiente. ➕ `pcc_lineWF_tracked_modulo_2` cablea los cinco. ⛔ `ind` (18) y `listInd` (20) **no salen**: sus `liftfc` van **anidados y bajo un `substfc`**, el evaluador pide `hasWitF (liftfc 1 A)` y la cascada sólo da `hasWitF A` ⇒ falta **`prf_hasWitF_liftfc`** (+ un nodo `tcm`) 🏁🏁🏁 **2026‑09‑10d‑e (§3.61‑§3.62): C3 CERRADO.** §10bis gana el nodo **`tcm : Term → STree`** (para los `termCodeM` **cerrados** de `ind`/`listInd`) — su dotado va por la **VÍA NUMERAL** (`prf_tc_termCodeM`), porque `tcFn (termCodeM x) ≐ termCode (termCodeM x)` es la ecuación **RETIRADA por inconsistente** —, y con `prf_hasWitF_liftfc` (fila 84h) cierra **`ind` (18) y `listInd` (20)** ⇒ **los SIETE**. ⭐⭐ §11ter paga el `hOther` que §11 y §11bis declararon **dos veces** «vacuo pero más honesto como hipótesis»: **era una excusa**. `pcc_tag_vacuous` lo cierra en **veinte líneas** con el mismo `ax_lineWF_inv` que ya se usaba (`prf_tag_absurd` transporta `lt ȷ̄ k̄` a `lt k̄ k̄` por Leibniz y `prf_lt_irrefl` explota) ⇒ 🏁 **`pcc_lineWF_tracked` INCONDICIONAL**, los 21 tags cableados. 🔑 **Regla**: una obligación declarada VACUA sin pagarla sigue contando como **ABIERTA** aguas abajo — ésta se arrastró como parámetro dos módulos y tres sesiones. |
| 84g | **`EvalLiftfcPrf`** | 🆕 **`pcc_eval_liftfc` · la base y la deuda MEDIDA** (2026‑09‑09b). `liftfcT` —la imagen dotada de `liftfc`, que **no existía**— entra como ⛔ **DEFINICIÓN** (postular su recursión como axioma objeto hace la teoría INCONSISTENTE); `liftfcT_termCode := rfl` la casa con `formCode`. Más `targetLiftfc` con su naturalidad, un control **negativo** (`fail_if_success rfl`: sin él el enunciado podría ser cierto por reflexividad) y las dos formas de la deuda **enunciadas, no postuladas**, con el puente `deuda_of_isFC1` que reusa el `∃∃` de C3‑F. ⚠️⚠️ **La medición que reclasifica una tarea**: `pcc_eval_liftc` sólo vale a nivel `zero` y `ax_liftfc_forall`/`_ex` **suben el nivel** ⇒ **A5 no es una generalización opcional: es prerrequisito de `pcc_eval_liftfc`**, y por tanto de los 4 tags que faltan. Footprint: sólo los tres axiomas de Lean. 🏁🏁 **CERRADO el 2026‑09‑09e (§3.53)**: `pcc_eval_liftfc` PROBADO, sin hipótesis, con `v` y `X` abstractos. Fontanería de `liftfcT` + las **8 ecuaciones dotadas** + el **chasis** (`pcc_eval_liftfc_modulo_8`) + los **8 casos**, net‑0. ⭐ Sale **un binder más barato** que el molde de B3.4: sin sustituyendo no hay `hasWit s` ni `HasWitLift`. ⚠️ Trampa medida: con el tag **variable**, el `numeralM k` **bloquea el cómputo de `substCodeF`** ⇒ el `hin` sale como parámetro. ⭐⭐ `CasoAtomL`/`CasoEqL` son donde **A5 cobra**: bajan al sorte TÉRMINO al nivel corriente |
| 84b | **`D3ChainDotPrf`** | 🆕 ⭐ **EL PUENTE ÁTOMO ↔ FORMA ACOTADA dentro de `Prov`, y D3 reducida a UNA obligación** (2026‑09‑08, rama **D**): `hC_dot_of_chainOkBDot` y `d3_prf_of_chainOkBDot`. Footprint = la base sancionada; **cero `axiom`**, la deuda se **enuncia** (`DEUDA_chainOkBDot`). ⚠️ **El hueco que `sondeos/A3IsFCBTracked.lean` no tenía**: allí `wfAll` **es** un `∀` acotado, así que `pcc_bdAll_intro` entrega justo lo pedido; aquí `chainOk` es un **ÁTOMO** (`Minimal/Axioms.lean:790`) y su forma acotada es otra fórmula. Cruzarlo **no** lo hace `prf_chainOk_iff_chainOkB` —ése es meta‑nivel—: hay que meter la implicación en la **teoría objeto** sobre código punteado y abierto, vía `pcc_thm_inst` + `prf_substfc_impl` + MP interna. ⛔ **Y mide lo que queda: D3 está AGUAS ABAJO de C3** — el `hbody` de `pcc_bdAll_intro` pide reflejar `lineWF`, o sea `pcc_lineWF_tracked`, que sólo existe como `_modulo_7`. ⭐ **Precisado 2026‑09‑08f**: esos 7 ya no piden las deudas de ADR‑020 (probadas) sino su condición **estructural** — 3 alcanzables hoy (fila 84f) y 4 esperando a `pcc_eval_liftfc`. 🏁 **2026‑09‑09f‑h (§3.55): D3 a DOS obligaciones.** §3 abre el destino (⛔ `chainOkBDot` **no reduce**: `substfc` es símbolo OBJETO; lo abre `prf_substfc_arith_open` hacia `substCodeF`) y fija su forma por `rfl`; §4 **el puente de la COTA** (⛔ el salto `(lenc p)˙ ↦ lencT ṗ` es la **ecuación de rastreo** y **sólo vale dentro de `Prov`**, vía `pcc_eval_lenc` + `PrfH_bdAllCode_congr_bnd`); §5 el `∃` acotado con **cota arbitraria** (⭐⭐ **más barato que el caso especial**: los pasos caros eran artefactos de la instancia); §6 el cuerpo del `∀` (⭐⭐ con `c := nil` el disyunto `In y nil` es **refutable** ⇒ su código puede quedar **arbitrario**, el único sitio de D3 donde el destino no impone la imagen); §7 el empaquetado; §8 el **`PsiF` exterior** y **`hmatch` descargado**; §9 **`hPinv_chainOkBPsi`** (footprint: sólo los 3 axiomas de Lean). ⭐⭐ Hallazgo que reordenó el frente: **los dos `PsiF` anidados hay que diseñarlos JUNTOS y de fuera adentro**. 🏁 **2026‑09‑09i (§3.56): siete de las NUEVE obligaciones de `pcc_bdAll_intro`, descargadas.** ⛔ Y primero una obstrucción **de enunciado, no de esfuerzo**: `hPl` (naturalidad del cuerpo) es **FALSA** para `chainOkBPsi ∘ tcFn`, certificado por dos `rfl` — `substCodeF` manda cada variable **al hueco o a un `varc` cerrado según su nivel**, y el `liftTerm` la mueve **fuera del hueco**. 🔑 De ahí **[ADR‑021](DECISIONS.md)** (y la MANDATORY **M‑7**): **el `PsiF` del chasis se escribe con símbolos OBJETO, nunca con un `substCodeF` sobre una fórmula que lleve el parámetro** (es lo que `argsInPsi` cumplía sin decirlo). ⇒ `chainOkBPsiDot`, con el código de la fórmula **cerrado**, y el puente a `chainOkBPsi` **dentro de `Prov`** con `prf_substfc_arith_open` — el de §3.55.1 **al revés**. ⭐ `hwPsi` cae entera con la rama C de ADR‑020 (el dividendo de dotar el cuerpo). 🏁 **2026‑09‑10 (§3.57): `hPsiId` PROBADO** con la **TERCERA variante** de la familia (`substtc_id_substCodeT`/`_Ts` + `substfc_id_substCodeF`), nivel actuante **por debajo** del `substCodeF`. ⚠️ Por debajo **el testigo deja de ser libre** —la casilla `n = v` es una `varc v̄` corriente y `substtc` la sustituye por él— ⇒ entra `u ≐ varc v̄`. ⭐⭐ Y el índice **no admite salto**: a `v+2` o más quedarían variables que `substtc` **decrementaría** y el enunciado sería **falso**; es exactamente «uno por debajo». 🧹 ADR‑019: `prf_liftc_varc0` pasa a ser la instancia `v := 0` de `prf_liftc_varc_numeral`, y `hW`/`hL_chainOkBPsi` se generalizan en `q`. 🏁🏁 **2026‑09‑10 (§3.58): `hwP` PROBADO en CUATRO líneas** — el KIT de ADR‑020 parte `hasWitF (bdAllBndCtx …)` en la cota (que cierra `hw_auto` sola) y el cuerpo, y el cuerpo se **transporta** del `PsiF` dotado al computable con **Leibniz OBJETO** (`prf_congr_hasWitF`) por el mismo puente. 🔑 **Tercera vez que el par dotado+computable paga**: §8 casó la FORMA, §10.5 transportó la PRUEBA, §12 el TESTIGO. ⇒ **`d3_prf_of_body_only`: D3 desde `hbody` Y NADA MÁS**. 🏁 **2026‑09‑10 (§3.59)**: `hbody` **partido en sus dos mitades** con la **composición de los dos `substfc`** (`substCodeF2` + `substfc_comp_substCodeF`) — el `PsiF` dotado es él mismo un `substfc`, así que componerlos es obligado; el resultado tiene **DOS huecos** y pide función meta propia. ⛔⛔ **Y con ello se CORRIGE lo que decía esta fila**: la mitad (b) **SÍ** depende del análisis por tags. Su cota lleva `premsOf` **dotado**, y `premsOf` no está definido por recursión sino por **21 axiomas, uno por TAG**, con pattern‑matching sobre la forma de la línea ⇒ para un argumento abstracto **no hay nada que evaluar**. Las dos mitades **no son independientes** y el orden correcto es **(a) primero**. ⬜ (a) `pcc_lineWF_tracked` (**5 de 7**) · ⬜ (b) `boundedPremsIn` (21 casos, aguas abajo de (a)) 🏁 **2026‑09‑10d‑e**: la mitad **(a)** sale del módulo (fila 84i) y la obstrucción de (b) queda **levantada a nivel objeto** (fila 84k) ⇒ lo que resta de (b) son **tres** piezas nombradas: B1 la reflexión punteada de `premsOf`, B2 el puente de la cota dentro de `Prov`, B3 el `pcc_bdAll_intro` interior. | 🏁 **2026‑09‑10h · §5bis/§5ter, la DEDUP (ADR‑019)**: `pcc_bdEx_carc_reflect_gen` —la §5 **generalizada en su `Phic`**, que se había escrito aguas abajo en `PremsBdAllPrf`— **baja aquí**, y `pcc_bdCarcLt_reflect` pasa a ser **su instancia** (vía `prf_contract`). ⚠️ **Generalizar era obligatorio, no estético**: el hueco a cambiar vive **bajo el binder del `exc`** y `pcc_rw` no llega ahí — el único sitio donde el salto se da es la obligación `hphi`, con el binder **ya abierto**. Y la hipótesis extra `A` tampoco es capricho: el consumidor real necesita la cota `j < lenc L` dentro de `hphi`, y por las tres hipótesis de §5 **no viaja**.
| 84h | **`LiftfcWitnessPrf`** | 🆕 🏁 **LA CLAUSURA DEL TESTIGO BAJO `liftfc`** (2026‑09‑10d, 657 l., **net‑0 PURO**): `prf_hasWitF_liftfc (v X) : hasWitF X ⇒ hasWitF (liftfc v X)`, con el **nivel libre**, que descarga `DEUDA_hasWitF_liftfc` (`EvalLiftfcPrf` §12). Dos armazones: `PHIL` (sorte TÉRMINO, conclusión **conjuntiva** sobre `liftc`/`liftsc`) y `PHILF` (sorte FÓRMULA), las dos por inducción fuerte de Cantor. ⭐⭐ **Y salió a un TERCIO del molde** (`prf_hasWitF_substfc`, 2 088 l.), que era lo que §3.60 había medido como «un FRENTE, sin atajo». Tres ahorros **medidos**: el caso `varc` es una **dicotomía cuyas dos ramas devuelven un `varc`** (`prf_liftc_varc_cases`) ⇒ testigo **incondicional**; **un binder menos** por armazón (no hay sustituyendo, luego ni `hasWit s` ni `HasWitLift`); y los casos `un` no necesitan `CRIT_hasWit_lift`. 🔑 La medida de §3.60 acertó en la **estructura** y falló en el **coste**, porque el molde ya había pagado y **exportado** toda la maquinaria genérica (`hasWitArgs`, `prf_hasWit_varc`/`_funcc`, las ocho inyecciones, `nilOrCons`). |
| 84i | **`D3BodyPrf`** | 🆕 🏁 **`hbody`(a) de D3 — la reflexión de `lineWF` en la cadena** (2026‑09‑10e). ⚠️ **Módulo aparte a propósito**: junta `D3ChainDotPrf` (que fija el destino) con `SubstTreeReflect` (que prueba el reflector) y **ninguno de los dos importa al otro**. Tres cosas: (1) `chainOk → chainOkB` y `∀`‑elim en `i` dan `lineWF (nthc q i)`; (2) `pcc_lineWF_tracked` da `Prov(⌜lineWF (nthc q i)⌝)` con el código en **reflexión pura**; (3) ⚠️ **la MONEDA** (§3.55.2 otra vez): el destino pide el **accesor dotado** `nthcT q̇ i̇`, y el salto lo paga `pcc_eval_nthc` **dentro de `Prov`** con Leibniz codificado, colapsando el `liftc` del binder (`prf_liftc_tcFn`). Dos mediciones por `rfl` antes de escribir: `lineWFDotAt q i = lineWFCodeFn (nthcT (liftc 0 q̇) i̇)` y `evalNthcCode p i = eqc (nthcT ṗ i̇) (nthc p i)˙`. **Incondicional** desde §11ter. Footprint = la base sancionada. 🏁🏁 **2026‑09‑10f (§3.65): B2, el PUENTE DE LA COTA.** §2 cruza `lencT (premsOfT (nthcT q̇ i̇)) ↦ (lenc (premsOf (nthc q i)))˙` en tres eslabones, con **B1** en el de en medio. ⚠️ Los dos primeros son **CONDICIONALES** ⇒ hay que reescribir a nivel **`PrfH`** (`PrfH_pcc_rw`, con `PrfH_leibniz_apply`), porque `pcc_rw` pide la igualdad interna como `Prf`. ⭐ Y la guarda `lineWF X` del eslabón de en medio la produce `prf_lineWF_of_chainOk` — **la misma pieza que usa la mitad (a)**: la dependencia que §13.1 midió, materializada en **una sola hipótesis**. §3 mide el destino por `rfl` (`premsDotAt_split`): **dos** capas de `liftc`, una por binder, que colapsan. |
| 84j | **`ListEtaPrf`** | 🆕 ⭐ **LA η DE LISTAS DESDE LA LONGITUD** (2026‑09‑10e, **net‑0 PURO**): `lenc L ≐ n̄ ⇒ L ≐ ⟨carc L, carc (cdrc L), …⟩` (`prf_eta_lenc`), más `prf_nil_of_lenc_zero`, `prf_eta_of_lenc_succ`, `prf_lenc_cdrc` y `prf_nthc1_carc_cdrc` (el **tag**, leído de la η). ⚠️ **No hay axioma que lo dé**: `ax_lineWF_cons` da **un solo piso** y sólo para líneas; el piso genérico sale de `prf_nil_or_cons` (inducción de listas) descartando la rama `nil` con `prf_succ_ne_zero`, y los pisos se apilan por recursión sobre `n`. Es el **prerrequisito** de evaluar `premsOf` sobre una línea abstracta (fila 84k). |
| 84k | **`PremsOfTagPrf`** | 🆕 🏁 **`premsOf` EVALUADO POR TAG — las 21 ramas, nivel OBJETO** (2026‑09‑10e, 417 l., **net‑0 PURO**). ⛔ **Levanta la obstrucción de §13.1/§3.59.2**: «los 21 `ax_premsOf_*` hacen pattern‑matching sobre un `cons` explícito ⇒ sobre una línea ABSTRACTA no hay nada que evaluar». **Cierto — mientras no se sepa la LONGITUD**, y la longitud sale del bicondicional del `ax_lineWF_*` del mismo tag. Cadena idéntica para los 21: tag ⇒ `lenc t ≐ n̄` ⇒ η (`prf_eta_lenc`) ⇒ la posición 1 **es** el tag (`prf_nthc1_carc_cdrc`) ⇒ `ax_premsOf_k` instanciado. ⭐⭐ **Medido, y a la BAJA**: «21 casos» sugería 21 pruebas; son **dos lemas genéricos** (`prf_lenc_of_tag`, `prf_premsOf_of_tag`), **dos envoltorios** y **ocho líneas por tag**. Generalizar salió más barato porque lo caro era la instancia, no el esquema. ⚠️ **Hallazgo**: `ax_lineWF_mp` es el **único** cuyo bicondicional **no lleva condición estructural** (su fidelidad la liga entera `ax_premsOf_mp`) ⇒ `_tag_plain` frente a `_tag_and`. ➕ `prf_of_premsOf_branches`, el ensamblador. ⚠️ Esto es el nivel OBJETO; la reflexión **punteada** (B1) va encima. |
| 84l | **`PremsOfDotPrf`** | 🆕 🏁🏁 **B1 · `premsOf` REFLEJADO DENTRO DE `Prov`** (2026‑09‑10f, 1 059 l.): `pcc_eval_premsOf (t) : lineWF t ⇒ Prov(premsOfT ṫ ≐ (premsOf t)˙)`, con `t` **abstracto**. Es el eslabón que a la cota de `hbody`(b) le faltaba (§13.1). Ruta = la de `pcc_eval_carc`: axioma **CODIFICADO** con testigos dotados → gemelo computable por `rfl` → los `liftc` **colapsan** → los `substfc` externos a mano → los **cerrados** dotados a nivel objeto → **transporte en cascada**. ⭐ El paso 6 es lo único nuevo y sale **genérico**: `pcc_rw_dot_consN` recorre una lista entera; ⚠️ su contrato sobre `G` es **más fuerte** que el de `pcc_rw` —hace falta que `G` **conmute** con `substfc`—, porque la recursión mete el prefijo `consT ẋ ·` DENTRO del contexto en cada piso. ⚠️ Cuatro medidas: con el tag **variable** `substCodeF` **no computa** (el `hcode` sale como parámetro, trampa de §3.53 otra vez); `nil` **es** `zero`; ⭐ **`implc a b` ES un `cons`** ⇒ el RHS de `mp` va con la MISMA cascada anidada dos veces, **cero maquinaria nueva**; y los `substfc` de aridad ≥3 actúan a **nivel > 0** pero **sin decrementos de índice**. |
| 84m | **`PremsBdAllPrf`** | 🆕 **B3 · el `pcc_bdAll_intro` INTERIOR de `boundedPremsIn`** (2026‑09‑10f, 580 l.): **ocho** de sus nueve obligaciones. ⭐⭐ **ADR‑021 se cumple SOLA aquí**, y eso **afina la regla**: en `premsPsi q i = substCodeF2 1 i̇' q̇' premsBodyF` el cuerpo es una fórmula **CERRADA** y los parámetros entran **sólo como TESTIGOS** ⇒ `hPl`/`hPs` son ciertas. En el exterior `q` viajaba **dentro** de la fórmula. 🔑 ⇒ lo que rompe la naturalidad **no es «ser un `substCodeF`»**, es que **el parámetro viaje dentro de la fórmula**. Piezas nuevas: `liftTerm_substCodeF2`/`substTerm_substCodeF2` (la naturalidad de `substCodeF2` en sus **dos** testigos, que no existía) y ⭐ **`substfc_id_substCodeF2`, la CUARTA variante** de la familia `substfc_inv_*` — nivel actuante uno por debajo del **más bajo** de los dos huecos. ⚠️ **El índice sigue sin ser cosmético** (van cinco): la guarda pasa de `liftFormula (v+2)` a **`(v+3)`**, porque entre el nivel actuante y el hueco alto hay **dos** casillas. `hwPsi` sale del par dotado/computable (cuarta vez que paga). 🏁🏁🏁 **2026‑09‑10g · LA NOVENA, PAGADA, Y `axiom d3` RETIRADO** (§9bis–§10, 1 392 l. en total): `DEUDA_premsBody` siguió la ruta medida —disyunto izquierdo **vacuo**, derecho por §5— y la **MONEDA de §3.55.2 pagó por cuarta vez**. Piezas nuevas: **`substfc_inv_substCodeF2`, la QUINTA variante** de la familia (nivel `v+1`, el hueco **bajo** de los dos — la más barata), `pcc_premsOfT_bridge`/`pcc_nthc_premsOf_bridge` y `prf_premsDisj_of_chainOk`. ⇒ **`d3_prf_real (φ)`** vive aquí (§10) y en `Meta/GodelTwo.lean` `axiom d3` pasó a **teorema** (**7 → 6 axiomas de Lean**). ⬆️ **2026‑09‑10h**: el genérico de §3 **bajó a `D3ChainDotPrf` §5bis** (ADR‑019); §3 conserva la **nota** de por qué hacía falta generalizar. |
| 84n | **`VerifierSound`** | 🆕 🏁 **MÓDULO E de `NegVerifier` · LA SOLIDEZ ESTRUCTURAL, EN DIEZ LÍNEAS** (2026‑09‑10h). `PLAN-NEGVERIFIER.md` §8 lo llamaba **«el corazón»**, riesgo **ALTO**, 300–500 líneas, y exigía un sondeo previo. ⭐⭐ **El sondeo (`sondeos/NegVerifierModE.lean`) midió que el corazón no había que construirlo**: el decisor que E necesita **no tiene que ser el verificador OBJETO**, basta el **decodificador META**, y entonces la solidez **ya estaba probada** — `verifier_sound` **es** `decodeChain_prf`. 🔑 La pieza que lo hace gratis es **`decodeForm_inj`**: el decodificador es una **SECCIÓN** («si decodifica, el código era real»), que es exactamente la *realidad hereditaria* que §8 pedía demostrar caso por caso. ⭐ La forma de consumo es la **CONTRAPOSITIVA** (`not_decodes_of_not_prf`): con `¬Prf φ`, la rama «cadena aceptada» del ensamblaje es **IMPOSIBLE**. ⬜ Lo que queda, **enunciado y no postulado**: `DEUDA_chainNeg` y `DEUDA_inNeg` (la **completitud negativa**), que `negVerifier_of_deudas` convierte en `NegVerifier`. ⛔ **Y el riesgo estaba al revés de como el plan lo ponía**: E era «ALTO» y es una línea; los que hay que rediseñar son **C y D**, porque los esquemas objeto **aceptan más que el decodificador** y `IsCodeShaped` **NO SEPARA**. Footprint de `verifier_sound`: **net‑0 PURO**. |
| 85–86 | `DiagonalTwo` · `GodelTwo` | infraestructura del punto fijo; **Gödel II `goedel_second'`**, módulo `axiom d3` |

🔁 = repatriado de `cuarentena/` el 2026‑08‑23 (§3.26).
*Status codes*: ✅ Complete · 🧊 Frozen · 🔶 Partial · 🔄 In progress · ❌ Pending

### 1.6 `cuarentena/` — ✅ VACÍA

Los **31** módulos que la reparación (ADR‑012/013) apartó **han vuelto todos**, con el footprint
sancionado y **sin cambiar ningún enunciado público**. El directorio conserva sólo su `README` como
registro del episodio. Ver [`cuarentena/README.md`](cuarentena/README.md) y §3.26.

> **6 `axiom` de Lean** (tras F7a): 3 esquemas de inducción (`Full/`), TFA (`Block8.ax_p_tfa`),
> 2 anclas de codificación (`ax_axiomsCodeT_eq` / `prf_axiomsCodeT_eq`), y `d3` (único postulado
> gödeliano vivo). Inventario en **[`AXIOMS.md`](AXIOMS.md)**. Ninguna es un `sorry` (ADR‑010).
>
> ⚠️ **La mitad `⊬¬G` de Gödel I sigue SIN cerrar.** `goedel_first_undecidable_numeral` toma
> `Reflects` como hipótesis META; descargarla exige **`NegVerifier`**.
> 🏁 **Estado 2026‑09‑10h**: el **módulo E** está hecho (`Meta/VerifierSound.lean`) y `NegVerifier`
> queda reducido a **dos deudas enunciadas** (`DEUDA_chainNeg`, `DEUDA_inNeg`), que son los módulos
> **C** y **D**. [ADR‑022](DECISIONS.md) estrechó la clase de testigos para que sean atacables.
> ⚠️ El plan `PLAN-NEGVERIFIER.md` sigue conteniendo afirmaciones falsas —van **tres** medidas—:
> **se re‑mide, no se lee**. **NO recuperar F7a.**

## 2 · Dependency Graph

```mermaid
graph TD
    subgraph FOL ["Project: FOL"]
        direction LR
        FOL_FOL["FOL.FOL"]
        FOL_Eq["FOL.Theorems.Eq"]
        FOL_Tactics["FOL.Tactics"]
    end

    subgraph RPP ["Project: ROBINSON_PlusPlus"]
        direction TB
        Axioms["Minimal/Axioms"]
        Block1["Block1"]
        Block2["Block2"]
        Block3["Block3"]
        Block4["Block4"]
        Block4_C5["Block4_C5"]
        Block4_C6_C7["Block4_C6_C7"]
        Block5["Block5"]
        Block6["Block6"]
    end

    FOL_FOL --> Axioms
    FOL_Eq --> Axioms
    Axioms --> Block1
    FOL_Tactics --> Block1
    Block1 --> Block2
    Block1 --> Block3
    Block2 --> Block3
    Block1 --> Block4
    Block3 --> Block4
    Block1 --> Block4_C5
    Block2 --> Block4_C5
    Block3 --> Block4_C5
    Block4_C5 --> Block4_C6_C7
    Block1 --> Block4_C6_C7
    Block4 --> Block4_C6_C7
    Block4 --> Block5
    Block4_C5 --> Block5
    Block4_C6_C7 --> Block5
    Block3 --> Block5
    Block5 --> Block6
    Block4 --> Block6
```

---

## 3 · Descripción de módulos — mapa de nodos temáticos

El detalle por módulo (definiciones, axiomas, firmas Lean 4, notación, dependencias) **ya no vive en
este índice raíz**, sino en los cinco **nodos temáticos** (`doc/REFERENCE-*.md`). Regla del árbol
REFERENCE (`AI-GUIDE.md` §0.5): el índice raíz cataloga y navega; los nodos documentan.

| Nodo | Cubre | Secciones |
|------|-------|-----------|
| [**Núcleo**](doc/REFERENCE-Kernel.md) | `Minimal/Axioms` — teoría objeto FOL⁼ (Q++), esquemas del verificador, capa Δ₀ | §3.1 |
| [**Aritmética**](doc/REFERENCE-Arithmetic.md) | `Block1–8` — aritmética desarrollada, Cantor, pares, listas, primos/TFA objeto | §3.2–§3.11 |
| [**Gödelización**](doc/REFERENCE-Godelization.md) | `Meta/Godel`, `Meta/Provability` — Nivel B/C (`⌜·⌝`, `formCode`, `Provable`) | §3.12–§3.13 |
| [**Full**](doc/REFERENCE-Full.md) | `Full/` — inducción general, representabilidad, `numeral`, TFA | §3.14 |
| [**Incompletitud**](doc/REFERENCE-Incompleteness.md) | Nivel D: Gödel I/II, D1–D3, Σ₁‑completitud provable (12‑A), módulos A/B de `NegVerifier`, **la REPARACIÓN (§3.24), la ESCALERA (§3.25), la REPATRIACIÓN (§3.26), el FRENTE `substfc` por la vía CERO AXIOMAS (§3.27) y el DESCENSO cerrado (§3.28)** | §3.15–§3.32 |

**Navegación fuerte:** cada nodo enlaza de vuelta a este índice, a sus nodos hermanos relacionados y a
los ficheros `.lean` que documenta. El subsistema **activo** es
[Incompletitud](doc/REFERENCE-Incompleteness.md) — su **estado vivo** es **§3.28**: el frente
`substfc` por la vía de **CERO AXIOMAS**, con la partición en tres predicados (que **discrimina**),
el reflector completo, el testigo para toda fórmula, la clausura bajo `liftc` y —desde el
2026‑08‑30— el **`DESCENSO` PROBADO**, que **es** `pcc_eval_liftc` (§3.28.1). El `PHI_guarded` del
consumidor **pasa el gate** de `prf_strong_induction` sin binder nuevo.
✅ **Y desde el 2026‑08‑30 los OCHO constructores de `substfc` están CUBIERTOS** (§3.29): los cinco
mecánicos (`botc` `implc` `andc` `orc` `exc`) y los dos duros, vía `pcc_eval_substtc'` y
`pcc_eval_substtsc'`. Los tres binarios salieron con **una sola prueba**, porque
`ax_substfc_impl/_and/_or` son la misma fórmula salvo el tag (certificado por `rfl`).
⚠️ **Cubiertos ≠ ensamblado**: falta la inducción que junta los ocho casos, y todo vive en
`sondeos/` con el coste de promoción de §3.28.5 sin pagar. Ver §5.

⚠️ **§3.15–§3.23 son ANTERIORES a la reparación** (ADR‑012/013). Lo que dicen de la capa rastreada
describe fielmente el código de `cuarentena/`, pero **ese código no está en el build** y sus
enunciados cambiarán al repatriarse. §3.15 documenta un **módulo eliminado** (`Meta/Incompleteness.lean`,
borrado en F7a) y está marcado como tal.

---

## 4 · Patterns notables y deuda técnica

- **Patrón `spec + simp`**: cada axioma instanciado vía `spec h_axN t` requiere un `simp` con simp-set propio según los binders del axioma. Para axiomas `forall_2` se necesita `liftTerm`/`FOL.substTerm_liftTerm`; para `forall_3`, además `FOL.substTerm_liftLift`. Ver `THOUGHTS.md` y `feedback_build_cache` en memoria de Claude.
- **`Γ` por módulo**: cada módulo define `def Γ := axioms`. La unificación entre `Block2.Γ` y `Block4_C5.Γ` falla con `apply` pero pasa con `exact` (defeq).
- **`=eq` no-estándar `eq_trans`**: `eq_trans (h1:a=b)(h2:a=c):b=c`. Para `a=b, b=c → a=c` usar `FOL.derive_eq_trans`.
- **Linter `unusedSimpArgs` desactivado** en todos los módulos (2026-06-06): `set_option linter.unusedSimpArgs false` global. Previamente se hizo un barrido a `true` (411 → 0 warnings), que confirmó qué args de `simp` eran innecesarios; tras ello se decidió dejar el linter en `false` (puede dar falsos positivos bajo binders existenciales y se prefiere libertad para conservar args de `simp` por robustez). El build permanece con 0 warnings.

---

## 5 · Próximos pasos

Punto de reanudación: **[NEXT-STEPS.md](NEXT-STEPS.md)** → **[PLAN-FRENTE-A.md](PLAN-FRENTE-A.md)**.
Visión a largo plazo: [PLANNING.md](PLANNING.md). Libro: [PLAN-LIBRO.md](PLAN-LIBRO.md).

**Estado 2026‑09‑10h.** Build **142 jobs**, **128 módulos activos**, **61 `sondeos/`**, 0 sorrys,
**6** `axiom` de Lean (`d3` retirado el 2026‑09‑10g).

### Lo que está cerrado

1. **Gödel I — `⊬G`**: `goedel_first_numeral (hcon : ConsistentOmega) : ¬ Prf godelCN`
   (`Meta/DiagonalNumeral.lean`), sobre el punto fijo real `godelCN_fixedpoint`. Footprint = la base
   sancionada **menos `tc_cons`**.
2. **D1** ✅ `repr_pos'_prf` y **D2** ✅ `d2_prf` — reales, sobre el cálculo finitario `Prf`.
3. **La ESCALERA (a.2)** ✅ **4 de 4** (§3.25): `pcc_eval_add`, `pcc_eval_mul`, el atajo de `div2`, y
   **`pcc_dot_cons`**. Es la Σ₁‑completitud internalizada para argumentos abstractos.

### Los frentes abiertos — **todos MEDIDOS** (actualizado 2026‑09‑10h)

| # | frente | estado | qué lo bloquea |
|--:|---|---|---|
| ~~**1**~~ | ~~muro de `substfc` → `hC_dot` → **D3** → Gödel II → F7b~~ | 🏁🏁 **CERRADO** (2026‑09‑10e/g). Los **7 reflectores** probados ⇒ `pcc_lineWF_tracked` **incondicional** (C3); y **D3 DEMOSTRADA** (`d3_prf_real`) ⇒ `axiom d3` **retirado**, **7 → 6** | — |
| **2** | **`NegVerifier`** → `⊬¬G` | 🏁 **módulo E hecho** (`Meta/VerifierSound.lean`): `verifier_sound` **es** `decodeChain_prf`. 🏁 **[ADR‑022](DECISIONS.md)**: la clase de testigos **estrechada** a `StdLine` ⇒ las comparaciones son **paralelas por tipo, sin evaluar Cantor**. ⚠️ El paso 1.1 del plan (`canon_ne`) sigue siendo **FALSO**, y el sustituto correcto es por **VALOR** (`numTree_ne` + las cotas `consN_ge`/`codeNat_ge`, `sondeos/MedirF_Censo.lean`) | **los módulos C y D** — las dos deudas enunciadas `DEUDA_chainNeg` y `DEUDA_inNeg` |
| **3** | **`prf_axiomsCodeT_eq`** | el axioma que arrastra casi todo el árbol («net‑0 son CUATRO, no tres»). Es de otra naturaleza que los gödelianos: dice que el código de la lista de axiomas **es** la lista de códigos | no medido |
| **4** | 🆕 **`primAxioms`** ([ADR‑023](DECISIONS.md)) | 🏁 **9 de 11 CERTIFICADOS** (2026‑09‑10h). El propietario **ratificó** el movimiento `axiom ax_induction_prim : primAxioms ⊢ inductionFormula φ` + `ax_induction` como **teorema** — **no añade axioma, lo mueve**: siguen **6** | ⬜ los 2 restantes (ax21, ax24) piden una **segunda** sanción sobre `ax_mod2_alternation`, **no pedida**. ⚠️ Antes conviene medir si ese axioma es **derivable** (bajaría a **5**) |
| **5** | **recodificar símbolos por índice** | 📏 medido (`sondeos/RecodCoste.lean`): el **98‑99 %** del `formCode` de los axiomas del verificador son los nombres de símbolos (`ax_tc_zero`: 49 015 → ~708 nodos, **69×**). **Hoy no es cuello de botella** | nada. ⚠️ Una tabla pura **no es total** ⇒ codificación **etiquetada** |

⚠️ **La frase «(1) cuesta axiomas, es decisión del autor» ya NO vale** (era de 2026‑08‑23): el
frente 1 fue por la **vía de CERO axiomas** ([ADR‑015](DECISIONS.md)) y **está cerrado**. La razón
de fondo sigue en §3.27.1: axiomatizar **no era más caro, era OTRO TEOREMA** — sus axiomas entrarían
en `axioms`, `ax_axiomsCodeT_eq` los metería en `axiomsCodeT` y **G cambiaría**. Es la misma
distinción que gobierna [ADR‑023](DECISIONS.md): **certificar sobre un subconjunto no mueve la
frontera; cambiar `axioms` sí**.

### Alternativa siempre disponible

⚠️ Esta sección decía «consolidar **Gödel II módulo el axioma D3**». **Ya no aplica**: `d3` es
teorema desde el 2026‑09‑10g. Lo publicable hoy es **más**: Gödel I `⊬G` real sobre la teoría
reparada, **D1, D2 y D3 las tres demostradas**, y Gödel II sin ningún postulado gödeliano —
`goedel_second'` conserva tres hipótesis explícitas que **no** son condiciones de derivabilidad.
Lo único que sigue abierto de Gödel I es la mitad **`⊬¬G`** (frente 2).

---

**Author**: Julián Calderón Almendros

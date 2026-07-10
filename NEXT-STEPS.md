# Next Steps — ROBINSON_PlusPlus

---

## ▶ PUNTO DE REANUDACIÓN (para retomar el trabajo — leer PRIMERO)

**Última tarea abierta:** cerrar **D3 / Segundo Teorema de Gödel** vía la **Σ₁‑completitud provable estándar** (plan **12‑A**: capa numérica Δ₀ del verificador). **Fases 1a, 1b y 2 ✅ COMPLETAS** (2026‑07‑08) — **quedan las fases 3, 4 y 5**.

**Para arrancar una sesión nueva, leer en este orden:**

1. **`MEMORY.md`** (índice de memoria; carga los `project_*.md` / `feedback_*.md`) — estado global y hallazgos.
2. **Este `NEXT-STEPS.md`** (bloque de reanudación + "Last updated") — qué está hecho y qué sigue.
3. **`GODEL-D3-TRACKED-DESIGN.md` §12–§14** — plan 12‑A por fases, veredicto del sondeo de la fase 2 (§13) y **§14.4 lecciones De Bruijn acumuladas** (leer SIEMPRE antes de escribir `PrfH`).
4. **`REFERENCE.md` §3.18** — proyección completa de la capa Δ₀ (`NumListPrf`, `NatArithPrf`, `BoundedInPrf`, `RunFnBoundedPrf`, `ChainOkBoundedPrf`).
5. **`ESCALANDO_EL_PROYECTO.md`** — enlace con el proyecto hermano DeepArith sobre el kernel FOL⁼ común.

**Estado (2026-07-09, 60 módulos, 74 jobs, Lean v4.31.0, 0 errores, 0 warnings, 0 sorrys; 7 `axiom` tras F7a — ver `AXIOMS.md`):**

- ✅ **Gödel I REAL** sin postulados (`goedel_first_real'`); **D1** (`repr_pos'_prf`) y **D2** (`d2_prf`) reales; `d3_prf_of_sigma1` (D3 reducida a `hC`/`hI`).
- ✅ **12‑A fases 1a/1b/2**: el verificador (`chainOk c p` y `In · (runFn nil p)`) está **expresado en la capa numérica Δ₀ y sin acumulador**. Era el único punto del plan sin verificar en código; ya no queda ninguno.
- 🔄 **Fase 3 ARRANCADA** (`Meta/Sigma1BoundedPrf.lean`, §15 del diseño): **puente `d3_prf_of_reflect_bounded`** — D3 reducida (vía `pcc_imp` + los `⇔` de fase 1/2) a reflejar la forma **Δ₀ acotada** `boundedIn`/`chainOkB` (`prf_hI_of_reflect_boundedIn`, `prf_hC_of_reflect_chainOkB`). La obstrucción de Tarski queda reubicada en el **átomo** `nthc L i =eq x`, que resuelven las ecuaciones de variable de `substfc`.
- ✅ **Fase 3 núcleo — átomo `=eq` CERRADO, LIBRE DE MURO** (`Meta/Sigma1AtomPrf.lean`, §15.3‑§15.4 del diseño). Clave: el verificador comprueba `lineWF` **estructuralmente** (`lineWF ⟨concl,12,t⟩ ⇔ concl =eq eqc t t`, y `eqc = eqCodeFn`), así que la **línea‑axioma EQREFL** `⟨eqCodeFn c c, 12, c⟩` es válida por **pura reflexividad** para `c` arbitrario, sin `termCode`. De ahí: **`prf_provFromCode_eqCodeFn_refl (c)`** (reflexividad libre de muro, testigo de una línea) y **`pcc_eq_tracked (t u) : Prf ((t =eq u) ⇒ provFromCode (eqCodeFn (tcFn t) (tcFn u)))`** (libre de muro, vía congruencia de `tcFn` + Leibniz object). Los tres `#print axioms = [propext, choice, Quot.sound]` — **desaparece hasta `prf_inAxC`**. El muro de Tarski queda confinado al último paso (`pcc_eq_of_tc_bridge`: puente `tcFn t =eq termCode t`, descargable con numerales en fase 5).
- ✅ **`atom1CodeFn` + `lineWFCodeFn`** (constructores de código de átomos unarios + transporte), `Meta/Sigma1AtomPrf.lean`.
- ✅ **OBSTRUCCIÓN §16 RESUELTA (sancionada):** `lineWF`/`premsOf` no estaban determinados (21 bicondicionales indexados por etiqueta, sin inversión). Añadido **`ax_lineWF_inv`** a `Minimal/Axioms.lean` (`lineTag`/`tagDisj` + el axioma, al final de `axioms` **y** `codingAxioms`) + cierre `Prf` **`prf_lineWF_inv`**. Verificado tras tocar el núcleo: `axioms_eq` sigue `rfl`, la cadena real **no cambia** (`goedel_second'` sólo `d3`), y los **7 `axiom` de Lean no cambian** (es un `def ax_*` de la teoría objeto).
- ✅ **SEGUNDA OBSTRUCCIÓN §17 RESUELTA: `pcc_exIntro_code'` (`hw` era innecesaria).** Pieza clave: **`liftTerm_substfc_open`** (`liftTerm c (substfc zero w Ac) = substfc zero (liftTerm c w) Ac`, con `Ac` cerrado) — el lift **atraviesa** y queda sobre el testigo. Así el contexto tras `prf_ex_elim_imp` es idéntico con `w' := liftTerm 0 w` y el ensamblaje `p ++ [q2line, mpline]` pasa **verbatim** (`prf_lineOk_q2` admite cualquier testigo). `[propext, choice, Quot.sound]`. El viejo `pcc_exIntro_code` se conserva como **corolario** (retrocompatible). **Verificado:** `pcc_exIntro_code' Ac (tcFn #0) hAc` typechequea — testigo **abierto** y **rastreado**.
- 📌 **De RIESGO‑1 cae exactamente la mitad (a)** — `tcFn #0` no cerrado ⇒ `hw` falla — **disuelta**. La mitad **(b)**, el transporte `tcFn L =eq termCode L` (Tarski genuino), **sigue viva pero confinada** al último paso (§15.4), descargable con numerales (`prf_tc_numeral`) en la inducción de fase 5. Sin sobre‑afirmar.
- 📌 **§18 (sondeo verificado): la reflexión de `<` NO es un ladrillo pequeño.** `=eq` está cerrado (§15.4) y el `∃`‑intro admite testigo abierto (§17.2), **pero no encajan**: `pcc_eq_tracked` produce el código con `tcFn` del **término entero** (= numeral del *valor* `a+σk`), mientras el cuerpo del `∃` de `ax13` necesita el código del **término simbólico** `ȧ + σj̇`. Son códigos distintos. `tcFn` (= `num`) sólo tiene 3 ecuaciones (`zero`/`succ`/`cons`) y **no debe** computar sobre `add`. El puente es **`⊢ Prov(⌜ȧ + σk̇ = (a+σk)˙⌝)`**: la **evaluación provable**, que se prueba por inducción interna. Es «la bestia» de §11.3.
- ✅ **Ladrillo entregado hacia ella:** **`liftFormula_provFromCode_open (k c) : liftFormula k (provFromCode c) = provFromCode (↑c)`** (`Meta/TrackedCorePrf.lean`) — generaliza la clausura a **códigos abiertos**. La necesita el **∀‑elim de código** (`prf_lineWF_q1` es estructural, como la línea Q2), donde el código abierto cae en el **consecuente** — al revés que en `pcc_exIntro_code'`. Imprescindible para **instanciar axiomas codificados** (p. ej. `ax13`) en la prueba interna.
- ⏳ **ORDEN CORRECTO (§18.3):** (1) **evaluación provable** (`⊢ Prov(⌜ṫ = v̇⌝)` para `+`, `σ`, `lenc`, `nthc`, `carc`, `runFn` sobre numerales; inducción interna) → (2) reflexión de `<` (corolario de (1) + `=eq` + `∃`‑intro) → (3) cuantificadores acotados + inducción estructural → `hbI`/`hbC` → `d3_prf` → `goedel_second_prf`. Ladrillo intermedio: **`pcc_forallElim_code'`** (∀‑elim de código, ya con su clausura resuelta).
- ⚠ **Nota honesta:** 12‑A ≈ portar la Σ₁‑completitud provable de IΣ₁; es trabajo de varias sesiones. **Alternativa siempre disponible:** consolidar Gödel II *módulo el axioma D3* (`goedel_second'`) — estado ya publicable.
- 🧹 **F7a ✅ HECHA** (2026‑07‑09): 14→7 `axiom`; `Meta/Incompleteness.lean` eliminado + 5 postulados de `Provability` retirados; registro en `AXIOMS.md`. **F7b** (`GodelTwo.d3`) bloqueada hasta D3 real.

> **HISTÓRICO (contexto de cómo se llegó aquí).** Lo que sigue en este bloque documenta el camino descartado (`tcFn`/Opción A) y el diagnóstico que llevó a 12‑A. Se conserva porque explica *por qué* la vía actual es ineludible; **no es la tarea abierta**.

**⚠ HALLAZGO (muro del testigo abstracto):** el puente cierra sólo para testigos **cerrados** (`tcFn p` cerrado sii `p` lo es → `hw` de `pcc_exIntro_code` se descarga). Para el testigo **abstracto** (`p = #0` tras `prf_ex_elim_imp`), `tcFn #0` NO es cerrado (`hw` falla) y, además, todo combinador base (`pcc_in_*`/`pcc_imp`/D1) produce códigos vía `termCode` **meta**; transportar a `tcFn` exige `tcFn L =eq termCode L`, **meta‑stuck para `L` abstracta**. **Conclusión: `hI_tracked` abstracto requiere la Opción A DE RAÍZ** (redefinir `provFormulaC'ₜ`/`provCodeC'ₜ` con `tcFn`/`substfc` desde el cuerpo Σ₁ + re‑derivar D1ₜ `repr_pos'_prfₜ`), no un lema incremental. Ver `GODEL-D3-TRACKED-DESIGN.md` §4.2.

**Próxima acción concreta (Opción A de raíz — plan detallado en `GODEL-D3-TRACKED-DESIGN.md` §10):**

0. ✅ **HECHO** (commit `fac8668`) `Meta/TrackedCorePrf.lean`: **`liftFormula_provFromCode`** (clausura genérica de `provFromCode c` para código cerrado arbitrario).
1. ✅ **HECHO** (commit `7fb9052`) **constructores `tcFn`‑based**: `atom2CodeFn` (generaliza `inFormCodeFn` a átomos‑2) + puente `formCode` + `inFormCodeFn_eq_atom2` + congruencia + clausura + transporte + `chainOkCodeFn`/`allInCodeFn`. §10.4 pasos 1‑2.
2. ⚠️ **`tcFn` (Opción A §10) DESCARTADO para el paso abstracto** (investigación §11, 2026‑07‑05c): el sondeo del caso cabeza de `hI_tracked` muestra que el consecuente `provFromCode(atom2CodeFn (tcFn·)(tcFn·))` sólo se identifica con el teorema real si `tcFn L =eq termCode L`, **stuck para `L` abstracta** (`tcFn` no tiene ecuación de variable). Además se verificó que **NO hay atajo por teorema de deducción** (D1 `repr_pos'` exige `Prf` CERRADO; D1‑con‑contexto es FALSA — esa brecha ES D3). Los constructores `atom2CodeFn` (`7fb9052`) siguen válidos como infraestructura.
3. ⏳ **VÍA GENUINA — Σ₁‑completitud provable estándar, diseño de codificación resuelto (§12)**: la vía testigo‑lista naíf **también se descartó** (§12.2: el paso cola mezcla testigos `tcFn rest` vs `tcFn (cons line rest)` → `pcc_imp` no aplica). **Hallazgo central (§12.1): la codificación del testigo ≡ la representación del verificador** — la Σ₁‑completitud estándar exige `δ` Δ₀‑sobre‑NÚMEROS (∃/∀ acotados), pero el verificador es estructural sobre listas (`carc`/`cdrc`, sin `len`/`nth`). **Recomendación §12.4 = Opción 12‑A (β‑función / capa numérica Δ₀ del verificador)**: grande pero segura (construcción de libro). Plan por fases §12.4:
   - **1a ✅ HECHO (commit `3eaffd8`)**: `lenc`/`nthc` (long./índice de lista‑código) — defs + 4 axiomas en `Minimal/Axioms` (extensión conservadora; `axioms_eq` rfl preservado; build entero verde, verificador/D1 intactos) + ecuaciones `Prf` (`Meta/NumListPrf.lean`: `prf_lenc_nil/cons`, `prf_nthc_zero/succ`).
   - **1b ⏳ EN CURSO** (más grande de lo estimado — es la puerta a reconstruir aritmética en `Prf`): la caracterización acotada `In x L ⇔ ∃ i < lenc L. nthc L i =eq x` necesita **primero un toolkit aritmético de `<` en `Prf`**, porque `<` = `∃k. a+σk=b` (`ax13`) y `add` recurre por la derecha, así que `0+n=n` NO es teorema de Q (necesita `Prf.ind`). **✅ TOOLKIT `<` COMPLETO** (`Meta/NatArithPrf.lean`, commits `2d7c17c`/`80bb08b`/`5e2ce47`/`d655e3c`; **todos `[propext, choice, Quot.sound]`**): `prf_nat_induction` (eliminador de inducción natural, envuelve `Prf.ind`); `norm11` (norm De Bruijn de 1 binder); `prf_add_zero_left` (`0+n=n`), `prf_add_succ_left` (`σm+n=σ(m+n)`); `prf_lt_iff` (`lt a b ⇔ ∃k. a+σk=b`); `PrfH_lt_intro`/`prf_lt_intro`; `prf_succ_ne_zero`, `prf_succ_inj`; `prf_zero_lt_succ`, **`prf_succ_lt_succ_of_lt`**, **`prf_lt_of_succ_lt_succ`**, **`prf_not_lt_zero`**; `PrfH_eq_congr_succ`.
     **Lección De Bruijn (clave, reusar):** para eliminar un `∃` de una HIPÓTESIS usar **`prf_ex_elim_imp`** (lift simple, casa con el `↑a`/`↑b` que ya trae el cuerpo del `∃`), **NO `PrfH_ex_elim`** (liftea además el contexto → doble lift). Y al desplegar `ax13_lt_def` hay que incluir **`add`** en el simp‑set o el cuerpo del `∃` no reduce.
   - **1b ✅ COMPLETA (commit `154fbc3`, `Meta/BoundedInPrf.lean`; `#print axioms` = `[propext, choice, Quot.sound]`):** **`prf_In_iff_boundedIn (x L) : Prf (In x L ⇔ ∃ i < lenc L. nthc L i =eq x)`**. Piezas: `boundedIn`; `liftFormula_boundedIn_gen`/`substFormula_boundedIn` (empujan lift/subst a través de `boundedIn` — imprescindibles: la inducción de listas mete DOS binders y `boundedIn` contiene un `∃`); helpers `prf_boundedIn_head/tail/nil/cons`; congruencias `prf_lt_subst2`/`PrfH_lt_subst1`/`PrfH_eq_congr_nthc2`/`PrfH_eq_congr_pred`; **`prf_zero_or_eq_succ_pred`** (`n=0 ∨ n=σ(pred n)`) y **`prf_zero_or_succ`** (`NatArithPrf`); las dos inducciones + el `⇔`.
     **TRUCOS clave (reusar):** (1) los `∃`‑elim van en **lemas `Prf` autónomos** (`prf_ex_elim_imp`, lift simple) y se aplican con `PrfH.mp` dentro de la inducción — nunca `PrfH_ex_elim` (liftea el contexto → doble lift). (2) Para partir por casos un índice dentro de un contexto `PrfH` **sin `∃`**, usar el **predecesor** (`prf_zero_or_eq_succ_pred`): el testigo del caso `i=σ(pred i)` es directamente `pred i`.
   - **FASE 2 — RIESGO CERRADO ✅ (sondeo 2026‑07‑08, commit `4685366`, `Meta/RunFnBoundedPrf.lean`, §13 del diseño):** **NO hace falta β‑función.** `runFn nil p` **no es recursión con acumulador: es el *map* de `carc` sobre `p`** — probado: `prf_runFn_nil_cons : runFn nil (cons line rest) =eq cons (carc line) (runFn nil rest)` y `prf_lenc_runFn : lenc (runFn nil p) =eq lenc p` (cadena `prf_runFn_cons`→`prf_concat_nil_eq`→**`prf_runFn_weaken`** (saca el acumulador fuera)→`prf_concat_cons_eq`; axiomas limpios). ⇒ el acumulador nunca hay que construirlo: `In x (runFn nil p)` queda acotado por `lenc p`, y en `chainOk` el acumulador solo se usa vía `In y (·)`, que se reescribe como `∃ k < i. carc (nthc p k) =eq y`. Es la formulación Δ₀ clásica «prueba = sucesión de líneas justificadas por líneas anteriores». **Corrección a §12.3: llamarlo «β‑función» era pesimista; la capa `lenc`/`nthc` de la fase 1 basta.**
   - **FASE 2 — lado `In` ✅ CERRADO** (`Meta/RunFnBoundedPrf.lean`, commits `4685366`/`ffbcdb9`/`05cc4ab`; todos `[propext, choice, Quot.sound]`): `prf_runFn_nil_cons`, `prf_lenc_runFn`, **`prf_nthc_runFn`** (`i < lenc p ⇒ nthc (runFn nil p) i =eq carc (nthc p i)`; patrón `∀i` interno + `qconf` + `PrfH_spec`, como `prf_runFn_concat`) y el **payoff**: **`prf_In_runFn_iff : In y (runFn nil p) ⇔ ∃ i < lenc p. carc (nthc p i) =eq y`** — cota `lenc p`, acotado sobre `p` directamente.
   - **EN CURSO — FASE 2, lado `chainOk`** (plan preciso en `GODEL-D3-TRACKED-DESIGN.md` **§14.2‑14.3**; sin obstrucción vista): objetivo `chainOk c p ⇔ chainOkB c p` con `chainOkB c p := ∀ i < lenc p. (lineWF (nthc p i) ∧ ∀ j < lenc (premsOf (nthc p i)). (In (nthc (premsOf (nthc p i)) j) c ∨ ∃ k < i. carc (nthc p k) =eq nthc (premsOf (nthc p i)) j))` — **el acumulador se elimina generalizando en `c`**. Sub‑lemas: (a) `allIn c L ⇔ ∀ j < lenc L. In (nthc L j) c`; (b) `In y (concat c [x]) ⇔ In y c ∨ y =eq x`; (c) split del `∃k<σj`; (d) la inducción principal con **`∀c` interno**. **Dependencias: (a), (b) y (c) son mutuamente independientes; sólo (d) depende de las tres.**
     - **✅ (b) HECHA** (`Meta/ChainOkBoundedPrf.lean`): `prf_in_concat_iff` (cierre de `ax_L3_in_concat`), `prf_in_cons_nil_iff` (`In y [x] ⇔ y =eq x`) y **`prf_in_concat_singleton_iff : In y (concat c [x]) ⇔ In y c ∨ y =eq x`** — el paso que absorbe la conclusión de la línea actual en el acumulador.
     - **✅ (0) HECHA** (refactor compartido; no bloqueaba a nadie, pero (c) y (d) lo necesitan): **`boundedCarcLt y p b`** = `∃k<b. carc (nthc p k) =eq y` con **cota arbitraria** (`boundedCarcIn y p = boundedCarcLt y p (lenc p)`, `rfl`) + `liftFormula_boundedCarcLt`. Necesario porque en `chainOk` la cota es el índice de la línea (`σj`, `i`), no `lenc p`.
     - **✅ (c) HECHA** (`Meta/ChainOkBoundedPrf.lean`): **`prf_boundedCarcLt_cons_succ_iff : (∃k<σj. carc (nthc (cons line rest) k) =eq y) ⇔ (carc line =eq y ∨ ∃k<j. carc (nthc rest k) =eq y)`**, con las dos reintroducciones `prf_boundedCarcLt_cons_of_head` (testigo `0`) y `prf_boundedCarcLt_cons_of_tail` (reindexa `k ↦ σk`). Todos `[propext, choice, Quot.sound]`.
     - **✅ (a) HECHA** (`Meta/ChainOkBoundedPrf.lean`): **`prf_allIn_iff_boundedAllIn : allIn c L ⇔ boundedAllIn c L`** con `boundedAllIn c L := ∀ j < lenc L. In (nthc L j) c`. Reparto: todo el manejo del `∀j` se **confina en cuatro lemas `Prf` autónomos** (`prf_boundedAllIn_nil`, `_cons_head` = instancia `j=0`, `_cons_tail` = reindexa `j ↦ σj`, `_cons` = reintroducción con case-split de `j`), y las dos inducciones de lista (`prf_boundedAllIn_of_allIn` / `prf_allIn_of_boundedAllIn`) quedan triviales. Piezas nuevas: `PrfH_eq_subst_in1` (congruencia de `In` en el **elemento**), `liftFormula_boundedAllIn_gen`/`substFormula_boundedAllIn`, `liftFormula_allIn`/`substFormula_allIn` (rfl). Todos `[propext, choice, Quot.sound]`.
     - **✅ (d) HECHA** (`Meta/ChainOkBoundedPrf.lean`): **`prf_chainOk_iff_chainOkB (c p) : Prf (chainOk c p ⇔ chainOkB c p)`**. Inducción de listas sobre `p` con el acumulador **`∀c` interno** (`chainBPred`), instanciando la HI en `c ++ [carc line]`. Escalones: (1) `prf_boundedCarcLt_zero` + **`prf_premOk_cons_iff`** (el lema puntual que fusiona (b) y (c): `In y c ∨ ∃k<σi. carc (nthc (line::rest) k) =eq y ⇔ In y (c++[carc line]) ∨ ∃k<i. carc (nthc rest k) =eq y`) + defs `boundedPremsIn`/`lineOkB`/`chainOkB` + clausuras De Bruijn + `prf_chainOkB_nil`; (2) las dos mitades del paso `cons` — `prf_lineOkB_zero_iff` (`i=0` ⇒ es `lineOk c line`, vía (a) + `prf_boundedPremsIn_zero_iff`) y `prf_lineOkB_cons_succ_iff` (`i=σi'`, vía `prf_boundedPremsIn_cons_succ_iff` + Leibniz `PrfH_congr_lineOkBAt`); (3) `prf_chainOkB_cons_iff` (espejo exacto de `ax_chainOk_cons`) + la inducción. Todos `[propext, choice, Quot.sound]`.
   - **✅ FASE 2 COMPLETA.** `chainOk`/`In (runFn nil p)` ya tienen forma Δ₀ sobre índices: `chainOkB c p := ∀ i < lenc p. (lineWF (nthc p i) ∧ ∀ j < lenc (premsOf (nthc p i)). (In (nthc (premsOf (nthc p i)) j) c ∨ ∃ k < i. carc (nthc p k) =eq nthc (premsOf (nthc p i)) j))`. **El acumulador ha desaparecido.**
     **Lecciones De Bruijn acumuladas (§14.4, REUSAR):** `∃`‑elim de una HIPÓTESIS → lema `Prf` autónomo con **`prf_ex_elim_imp`** (nunca `PrfH_ex_elim`, liftea el contexto). `∀`‑intro como CONSECUENTE → **`Prf.qconf`** (nunca `PrfH.gen`). `∀`‑elim de una hipótesis → `PrfH_spec`. Case‑split de un índice bajo `PrfH` sin `∃` → `prf_zero_or_eq_succ_pred` (testigo `pred i`). Empujar lift/subst a través de un predicado con `∃`/`∀` interno necesita lema propio (NO es defeq; los iguala `FOL.liftTerm_comm_zero`). En un `have`, `PrfH _ (…)` no infiere Γ → nombrar el contexto con `let`.
   - **Fases 3‑5:** `num` (numeral‑de) + provable eval + Δ₀‑completitud atómica (aquí entran las ecuaciones de variable de `substfc`); inducción estructural → `⊢ ∀p (δ → Prov ⌜δ(ṗ)⌝)`; ∃‑intro (`pcc_exIntro_code`) → `d3_prf` → `goedel_second_prf`. NOTA: 12‑A ≈ portar la Σ₁‑completitud provable de IΣ₁ (multi‑sesión). **Enlace estratégico:** ver `ESCALANDO_EL_PROYECTO.md` (este toolkit sirve también a DeepArith sobre el kernel FOL⁼ común).
4. **Alternativa honesta siempre disponible (§11.4):** consolidar Gödel II **módulo el axioma D3** (`GodelTwo.goedel_second'`) — estado ya excelente/publicable (Gödel I real + D1/D2 reales). D3 es notoriamente la pieza más dura de Gödel II.
5. **Limpieza F7 — auditoría 2026‑07‑08 la parte en dos:**
   - **F7a ✅ VIABLE AHORA** (verificado con `#print axioms`): `goedel_second'` NO cita `diagonal_lemma`/`provFormula_repr`/`Dem`/`Incompleteness.D2`/`Incompleteness.D3`. Esos 7 postulados solo los usa la **capa legacy** (`Provability.goedelSentence` + teoremas legacy de `Incompleteness.lean`); las menciones en `Necessitation`/`Diagonal`/`HilbertSeq` son solo docstrings. Retirarlos (junto con los teoremas legacy) **no toca la cadena real** y bajaría de 14 a 7 `axiom` de Lean.
   - **F7b ⛔ BLOQUEADA:** `GodelTwo.d3` sí es portante (`goedel_second'` lo cita). Espera al D3 real.

> **Estado real de la cadena (auditado 2026‑07‑08 con `#print axioms`):** D1 `repr_pos'_prf` = estándar + `prf_inAxC`; **D2 `d2_prf` = estándar, cero postulados**; `d3_prf_of_sigma1` = estándar + `prf_inAxC`; **Gödel I real** `goedel_first_real'` = estándar + ω‑reglas + `ax_induction`/`ax_list_induction`/`ax_inAxC` (ningún postulado gödeliano); **Gödel II** `goedel_second'` = estándar + ω‑reglas + `ax_list_induction` + **`d3`** (único postulado gödeliano). Los 4 axiomas `lenc`/`nthc` añadidos a `Minimal.axioms` son `def ax_*` de teoría object (extensión definicional conservadora), NO `axiom` de Lean.

<!-- -->

> **Nota De Bruijn (reusar en `hI/hC_tracked`):** colapso de lift con DOS ubicaciones OPUESTAS. (1) Contexto post‑`prf_ex_elim_imp`: `liftTerm 0 (substfc zero w Ac)` sin subst externa → colapsar con `simp only [liftTerm_substfc …]` PREVIO al `simp` grande, MIENTRAS `zero` es literal. (2) Target post‑`PrfH_ex_intro`: `liftTerm 0 (exc Ac)` se cancela con la subst externa `substTerm 0 r (·)` (`FOL.substTerm_liftTerm`) → NO pre‑colapsar. (`substTerm v s (.var v) = s` sin lift, FOL.lean:82.)

**Recordatorios de build (ver `feedback_*`):** compilar SIEMPRE desde RPP bajo v4.31.0 (nunca `cd FOL && lake build`); un build "Replayed" de caché puede ocultar errores en ediciones sin commitear.

---

**Last updated:** 2026-07-08 (61 módulos, 75 jobs, Lean v4.31.0, 0 sorrys) — **12‑A FASES 1b y 2 COMPLETAS: el verificador ya es Δ₀ y sin acumulador.** Cuatro módulos nuevos: `Meta/NatArithPrf.lean` (toolkit de `<` en `Prf`; `0+n=n` **no** es teorema de Q → `Prf.ind`), `Meta/BoundedInPrf.lean` (**`prf_In_iff_boundedIn`**), `Meta/RunFnBoundedPrf.lean` (**`prf_In_runFn_iff`**; hallazgo: `runFn nil p` es el *map* de `carc` ⇒ **no hace falta β‑función**, corrige el pesimismo de §12.3) y `Meta/ChainOkBoundedPrf.lean` (**`prf_chainOk_iff_chainOkB`**: *el acumulador desaparece*, inducción con `∀c` interno + lema puntual `prf_premOk_cons_iff`). Todos `#print axioms` = `[propext, choice, Quot.sound]`. Ya **no queda ningún punto del plan 12‑A sin verificar en código**. Siguiente: fases 3‑5 → `d3_prf` → `goedel_second_prf`. — (previo 2026-07-05, ~54 módulos, 67 jobs) **Opción A: predicado de demostrabilidad con TESTIGO RASTREADO (hacia D3/Gödel II)**. Tras caracterizar rigurosamente el muro (`hI`/`hC` genéricos son indemostrables: el código absorbe el testigo `#0` como `varc 0`, reflejando una fórmula con variable libre que no es teorema), se adoptó **Opción A** (rastreo uniforme vía `tcFn`/`substfc`, patrón `diag_arith`). Diseño completo en **`GODEL-D3-TRACKED-DESIGN.md`** (diagnóstico, opciones A/B, fases, riesgos). Hecho: **A‑F1** (`prf_tc_objList`/`prf_tc_objList_formCode`: `tcFn=termCode` sobre la forma de la lista de conclusiones) + **A‑F2** (**`prf_provCodeC'_of_tracked_witness`**: la reflexión rastreada con testigo-código = `provCodeC'` real; mecanismo central). También `pcc_in_runFn_objList` (= `hI` para testigos **concretos**) + tracking `runFn→objList`. **Próximo (A‑F3/F4, piezas grandes tipo `d2_prf`)**: `pcc_exIntro_code` (∃-intro a nivel de código para testigo-código arbitrario — **verificar primero** que el verificador acepta líneas-axioma Q2 con testigo arbitrario) + `hI_tracked`/`hC_tracked` por inducción object (consecuente `substfc 0 (tcFn p)` rastrea `p`) → `d3_prf` → `goedel_second_prf`.

**Last updated:** 2026-06-28b (~52 módulos, 65 jobs) — **Infraestructura de reflexión Σ₁ (núcleo duro de D3)**. `Meta/Sigma1Prf.lean` (NUEVO): combinador clave **`pcc_imp {A B} (h : Prf (A ⇒ B)) : Prf (provCodeC' A ⇒ provCodeC' B)`** (D2 `d2_prf` + D1 `repr_pos'_prf`) + `pcc_imp2` + combinadores `pcc_in_head/tail/head_eq/nil`, `pcc_chainOk_nil/cons`, `pcc_allIn_nil/cons`. Con ellos, `hI`/`hC` se reducen a **(1) reflexión de igualdad** `Prf ((x=eq y) ⇒ provCodeC'(x=eq y))` (obstrucción Tarski: los `▸`/Leibniz fallan porque `formCode(x=eq y)` absorbe la forma sintáctica de `y`, no su valor → necesita sustitución formalizada `substfc`) **y (2) cierre inductivo** sobre el código con seguimiento aritmético `tcFn`/`substfc` (la "bestia", Fase 5). CORRECCIÓN: la inducción object directa sobre `L` NO sirve (el código absorbe `#0` como numerales). **Próximo**: **reflexión de igualdad con `substfc`** (`substFormula_arith`/`prf_substTerm_arith` en SubstArith/ArithPrf) → `hI`/`hC` → `d3_prf` → punto fijo/necesitación en `Prf` → `goedel_second_prf`. — (hito previo) **D3 finitaria REDUCIDA: `d3_prf_of_sigma1` (Punto 6, paso 9)**. `Meta/ReflectionPrf.lean` (NUEVO), porte de `Reflection.lean` ω → `Prf`: combinadores `PrfH_pcc_mp`/`pcc_prf`/`pcc_andIntro`/`pcc_exIntro` (vía `d2_prf`+`repr_pos'_prf`) + **`d3_prf_of_sigma1 (φ) (hC) (hI) : Prf (provCodeC' φ ⇒ provCodeC'(provCodeC' φ))`** que reduce D3 a la **Σ₁-completitud provable del verificador** (hipótesis `hC`/`hI`), aislando el núcleo duro. `#print axioms` = `[propext, choice, Quot.sound, prf_inAxC]`. `Meta/ReflectionPrf.lean` (NUEVO), porte de `Reflection.lean` ω → `Prf`: combinadores `PrfH_pcc_mp`/`pcc_prf`/`pcc_andIntro`/`pcc_exIntro` (vía `d2_prf`+`repr_pos'_prf`) + **`d3_prf_of_sigma1 (φ) (hC) (hI) : Prf (provCodeC' φ ⇒ provCodeC'(provCodeC' φ))`** que reduce D3 a la **Σ₁-completitud provable del verificador** (hipótesis `hC : ∀p, Prf (chainOk nil p ⇒ provCodeC'(chainOk nil p))`, `hI : ∀x L, Prf (In x L ⇒ provCodeC'(In x L))`), aislando el núcleo duro. `#print axioms` = `[propext, choice, Quot.sound, prf_inAxC]`, sin postulados gödelianos. (Fix: `lean-toolchain` de la copia de trabajo estaba a v4.31.0 — rompía `simpa` de `Representability` al recompilar; restaurado al commiteado v4.29.1.) **Próximo (núcleo duro de D3)**: **`hI`** (el más tratable: inducción de listas sobre `L` — `nil` por explosión, `cons` por or-elim + `repr_pos'_prf` de `in_cons_head`/`in_cons_tail`) → **`hC`** (más difícil: `chainOk` = `lineOk`/`allIn`/`runFn`, construir código de prueba objeto por inducción sobre el testigo) → **`d3_prf := d3_prf_of_sigma1 φ hC hI`** → punto fijo + necesitación en `Prf` → **`goedel_second_prf : ConsistentH → ¬ Prf Con'`**. — (hito previo) **D2 FINITARIA REAL: `d2_prf` (Punto 6, paso 9)**. `Meta/DerivCondPrf.lean` (NUEVO): **`d2_prf : Prf (provCodeC'(A⇒B) ⇒ (provCodeC' A ⇒ provCodeC' B))`** (`#print axioms` = `[propext, Classical.choice, Quot.sound]`, sin postulados de derivabilidad). Tres piezas: **capa de clausura** (`liftTerm_numeral`/`charsCode`/`strCode`/`termCode`/`formCode` + `liftFormula_provCodeC'`: los códigos son cerrados — prerequisito porque `prf_ex_elim_imp` no da acceso meta al testigo); **`∃` en `PrfH`** (`PrfH_ex_intro`/`PrfH_ex_elim` vía `q2`/`q3` en `HilbertDeduction`, para testigos anidados `p=#1`,`q=#0`); **ensamblaje** `r=p++q++[mp]` con los lemas de cadena del paso 8. Helpers nuevos en `ChainPrf`: `prf_In_mono_right_imp`, `PrfH_allIn_subst2`, `PrfH_in_cons_head`. `Meta/DerivCondPrf.lean` (NUEVO): **`d2_prf : Prf (provCodeC'(A⇒B) ⇒ (provCodeC' A ⇒ provCodeC' B))`** (`#print axioms` = `[propext, Classical.choice, Quot.sound]`, sin postulados de derivabilidad). Tres piezas: **capa de clausura** (`liftTerm_numeral`/`charsCode`/`strCode`/`termCode`/`formCode` + `liftFormula_provCodeC'`: los códigos son cerrados — prerequisito porque `prf_ex_elim_imp` no da acceso meta al testigo); **`∃` en `PrfH`** (`PrfH_ex_intro`/`PrfH_ex_elim` vía `q2`/`q3` en `HilbertDeduction`, para testigos anidados `p=#1`,`q=#0`); **ensamblaje** `r=p++q++[mp]` con los lemas de cadena del paso 8. Helpers nuevos en `ChainPrf`: `prf_In_mono_right_imp`, `PrfH_allIn_subst2`, `PrfH_in_cons_head`. **Próximo (resto Punto 6)**: **`d3_prf`** (Σ₁-completitud provable — el más difícil; espejo de la D3 ω si existe, o `Reflection.lean`) → punto fijo + necesitación en `Prf` → **`goedel_second_prf : ConsistentH → ¬ Prf Con'`**. Limpieza opcional: retirar la vía legacy postulada (`Incompleteness.D2/D3`, `diagonal_lemma`, `GodelTwo.d3`). — (hito previo) **PASO 8 COMPLETO: los 10 lemas de cadena en `Prf`** (`runFn_concat`/`chainOk_concat`/`chainOk_mono`/`runFn_weaken`/`In_mono`/`In_mono_right`/`concat_assoc`/`allIn_mono`/`lineOk_mono`/`concat_nil_right`), frontera `∀c` resuelta de raíz vía `norm32`/`norm_s`/confinación-`qconf`. — (hito previo) **Lemas de cadena en `Prf`: eliminador + `prf_concat_nil_right` (paso 8, patrón validado)**. `Meta/ChainPrf.lean`: `prf_list_induction` + helpers `PrfH` (`PrfH_leibniz_subst`/`PrfH_eq_trans`/`PrfH_congr_cons_tail`) + primer lema de cadena `prf_concat_nil_right` (valida `base`+`step` vía `prf_deduction`; `#print axioms` = estándar). — (hito previo) **regla `listInd` integrada (paso 7 parte 2 COMPLETO)**. Vertical slice completo (`Prf.listInd`/`Rule.listInd` + doble aritmetización + `prf_listInd_concl_code` + cascada `vpf_run`/`chainOk_track`/`prf_chainOk_track` + `HilbertDeduction`); `repr_pos'_prf` honesto (`[propext, choice, Quot.sound, prf_inAxC]`). `Prf` tiene ahora inducción de listas. **Próximo (paso 8)**: port de lemas de cadena a `Prf` (`runFn_concat`, `chainOk_concat`, `In_mono`, `In_mono_right`, `concat_nil_right`, `runFn_weaken`, `chainOk_mono`) instanciando `listInductionFormula` con cada propiedad + `prf_deduction` para el paso → luego `d2_prf`/`d3_prf`/`goedel_second_prf : ConsistentH → ¬ Prf Con'`. — (hito previo) **`listInd_concl_code` (paso 7 parte 2, núcleo)**. `Meta/ListInductionArith.lean`: reconstrucción del código de `listInductionFormula A` desde ⌜A⌝ + `congr_liftfc_arg2` (más complejo que `ind`: `cons #1 #0` con variables libres). **Próximo (resto paso 7 parte 2)**: slice verificador `Prf.listInd`/`Rule.listInd` (stepConcl/ruleCode tag 20/prf_to_derivation + doble aritmetización legacy+runFn + versión Prf `prf_listInd_concl_code` + cascada lineJustif/lineCode/vpf_run/chainOk_track/prf_chainOk_track) → port lemas de cadena a Prf → `d2_prf`/`d3_prf`/`goedel_second_prf`. — (hito previo) **`list_induction_derives` (paso 7 parte 1)**. `listInductionFormula Φ` + `list_induction_derives : axioms ⊢ listInductionFormula Φ` en `Hilbert.lean` (vía `ax_list_induction`+ω-gen; antecedente del paso `subst_lift_same`, consecuente Barendregt `subst_subst_comm_succ`+`subst_subst_lift_gen`; `C' = substFormula 0 (cons #1 #0) (liftFormula 2 (liftFormula 1 Φ))`). **Próximo (paso 7 parte 2)**: slice `Prf.listInd`/`Rule.listInd` (verificador: stepConcl/ruleCode/prf_to_derivation + doble aritmetización legacy+runFn + `listInd_concl_code` con `termCode (cons #1 #0)` — variables libres, más complejo que `ind`) → port lemas de cadena a Prf → `d2_prf`/`d3_prf`/`goedel_second_prf`. — (hito previo) **lema de Barendregt → paso 7a COMPLETO**. `subst_subst_comm_succ` (+ versiones término) en `FOL/Theorems/Eq.lean`; con `subst_subst_lift_gen`+`subst_lift_same` se verifica end-to-end la identidad del consecuente de la inducción de listas objeto (`C' = substFormula 0 (cons #1 #0) (liftFormula 2 (liftFormula 1 Φ))`, antecedente `liftFormula 1 Φ`). **Próximo (paso 7)**: definir `listInductionFormula Φ` + probar `list_induction_derives : axioms ⊢ listInductionFormula Φ` (vía `ax_list_induction`+ω-gen+identidad consecuente) → slice `Prf.listInd`/`Rule.listInd` (tipo `qconf`) → port de lemas de cadena (`runFn_concat`/`chainOk_concat`/`In_mono`…) → `d2_prf`/`d3_prf`/`goedel_second_prf`. **Próximo (paso 7a→7)**: una composición subst–subst a nivel fórmula → formular `listInductionFormula Φ` + `list_induction_derives` (vía `ax_list_induction`+ω-gen) → slice `Prf.listInd`/`Rule.listInd` → port de lemas de cadena → `d2_prf`. Build verde (**60 jobs**), 0 sorrys. — (hito previo) **SOLIDEZ: eliminado un `axiom` FALSO de FOL (`subst_lift_cancel_formula`)**. El axioma De Bruijn general era falso (verificado) y todo el Nivel D lo citaba; ahora es teorema en su forma restringida verdadera `substFormula v (#v) (liftFormula (v+1) f) = f` (demostrado por inducción + helper de término mutuo). `confinement_derives` queda en `[propext, Classical.choice, Quot.sound]`. **Próximo (paso 7, retomado)**: formular `listInductionFormula` (esquema objeto de inducción de listas) con el `subst_lift_cancel_formula` ya fiable → `Prf.listInd`/`Rule.listInd` (slice tipo `qconf`) → port de lemas de cadena → `d2_prf`. Build verde (**60 jobs**), 0 sorrys. — (hito previo) **teorema de deducción finitario para `Prf`** (`Meta/HilbertDeduction.lean`). Nuevo `Meta/HilbertDeduction.lean`: cálculo con contexto `PrfH` (espejo finitario de `Prf`, `gen` de contexto-lift + `hyp`) + teorema de deducción (caso `gen` cerrado vía `qconf`) + `PrfH []↔Prf`. Exporta `prf_deduction : PrfH [A] B → Prf (A ⇒ B)` y `prf_ex_elim_imp : PrfH [A] (↑C) → Prf (∃A ⇒ C)` (eliminación del ∃ = `provCodeC'_elim` finitario). `#print axioms` = estándar. **Próximo (paso 7)**: regla/esquema de **inducción de listas en `Prf`** (slice análogo a `qconf`) → port de lemas de cadena (`runFn_concat`/`chainOk_concat`/`In_mono`...) → `d2_prf` → `d3_prf` → `goedel_second_prf`. Build verde (**60 jobs**), 0 sorrys. — (hito previo) **regla `qconf` (confinamiento ∀) integrada en el verificador**. Slice completo (tipo `ind`, sin postulados): `Prf.qconf`/`Rule.qconf` + ambas aritmetizaciones (legacy `validProofFn` y `runFn`) + casos en `vpf_run`/`chainOk_track`/`prf_chainOk_track`. `prf_iff_derivation` sigue total; `repr_pos'_prf` honesto (`[propext, choice, Quot.sound, prf_inAxC]`); `provCodeC'` rastrea `IΣ₁ + confinamiento ∀`. **Próximo (paso 6)**: teorema de deducción finitario para `Prf` (caso `gen` vía `qconf`) → regla de inducción de listas en `Prf` (slice análogo) → port de lemas de cadena (`runFn_concat`...) → `d2_prf` → `d3_prf` → `goedel_second_prf : ConsistentH → ¬ Prf Con'`. Build verde (**59 jobs**), 0 sorrys. — (hito previo) **confinamiento ∀ (`confinement_derives`)**. Arrancando `d2_prf` se topó el **muro del confinamiento ∀**: el teorema de deducción de `Prf` (Hilbert finitario) lo necesita en su caso `gen`, pero `Prf₀`/`Prf` están **congelados** por la completitud del verificador (`prf_iff_derivation`, base de `repr_pos'_prf`) — no se le puede añadir confinamiento como axioma sin romperla, y derivarlo por dualidad clásica es circular. Solución de libro (sin postulados): **`confinement_derives : axioms ⊢ ((∀(↑P ⇒ C)) ⇒ (P ⇒ ∀C))`** probado directamente en `Derives` (deducción natural), que justificará el esquema `Prf.qconf`/regla del verificador. Plan multi-fase: regla `qconf` (slice tipo `ind`: verificador + aritmetización) → regla de inducción de listas → teorema de deducción finitario → port de lemas de cadena (`runFn_concat`/`chainOk_concat`/`In_mono`...) → `d2_prf` → `d3_prf` → **`goedel_second_prf : ConsistentH → ¬ Prf Con'`**. Build verde (**59 jobs**), 0 sorrys. — (hito previo) **`repr_pos'_prf` COMPLETO (D1 re-nivelada a `Prf`)**. Toda la representabilidad positiva sube al cálculo finitario `Prf` (necesario para Gödel II real: `provCodeC'` rastrea `Prf`, `¬⊢Con'` es falso): **`repr_pos'_prf : Prf φ → Prf (provCodeC' φ)`** (`#print axioms` = estándar + único meta-axioma `prf_inAxC`, espejo del `repr_pos'` ⊢-level). Dos módulos nuevos: `Meta/ArithPrf.lean` (porte finitario de toda la aritmetización, ~50 lemas; hallazgo: `numeral_lt` es finitario —∃-intro vía `q2`— por lo que toda la aritmética de códigos sube a Prf) y `Meta/Representability2Prf.lean` (tracking `prf_runFn_track`/`prf_chainOk_track` 19 casos + `provCodeC'_intro_prf` + ensamblaje). En `Meta/ReprPrf.lean`: 32 esquemas `lineWF`/`premsOf` portados. **Próximo (cadena Gödel II en Prf)**: `d2_prf` (añadir regla de inducción de listas en `Prf`, como se hizo con `ind`) → punto fijo + necesitación en Prf → `goedel_second_prf` (`ConsistentH → ¬ Prf Con'`) → **D3 real**. Ver [GODEL-D-ARITHMETIZATION.md](GODEL-D-ARITHMETIZATION.md).

**(2026-06-19, 35 módulos, 49 jobs)** — **GÖDEL NIVEL D REAL — PRIMER TEOREMA DE GÖDEL REAL SIN POSTULADOS**. Cadena completa sobre el cálculo de Hilbert finitario `Prf`: verificador `validProofFn` sólido (18 reglas, `thy` vía `coreAxioms`) → `repr_pos`/**D1** (`Necessitation`) → **lema diagonal real** (`Diagonal`: `tc_arith` código-del-código → `diag_arith` → `godelC_fixedpoint : ⊢ G ⇔ ¬provCodeC G`) → **`goedel_first_real : ConsistentOmega → ¬ Prf G`**. Además aritmética negativa de códigos `formCode_ne` (`CodeDistinct`). `#print axioms` de los resultados = solo ω-reglas ambiente; ningún `diagonal_lemma`/`provFormula`/D2/D3.

**(2026-06-12)** — **TFA COMPLETO CERRADO** (existencia object ∧ unicidad ℕ, sobre numerales, autocontenido sin Mathlib/Peano): `tfa_numeral` (`Full/Factorization.lean`). Unicidad ℕ vía Euclides (`Full/PrimeFactor.lean`: `euclid`, `factorization_perm_unique`). Capa de teoría de números completa sobre la representabilidad: `Primality` (`isPrime_numeral`), `Division` (`division_numeral`), `PrimeFactor` (ℕ pura: factor primo, factorización, **Euclides + unicidad**), `Factorization` (`tfa_exists_numeral`, `tfa_numeral`). Cimientos: `Numerals` (homomorfismo `+,·,^,<,≠`), `Bounded` (`le_numeral_split`), `Divisibility` (`numeral_dvd`, `divisor_le`), F1 `StrongInduction`. Reencuadre **numerales + representabilidad** (Gödel-aware) disuelve los Muros 1/2. Fragmento aritmético + listas de Minimal en Full: ax6/7/10–12, ax18/19, ax21/24, ax_C3/L3 ✅. Sistema con **34 axiomas matemáticos** en Minimal + meta-axiomas, **24 módulos** (Minimal/ 11 + Meta×2 + Full ×11), 0 sorrys, 0 warnings (37 jobs). **Próximo**: Gödel Nivel D (Meta/Incompleteness) sobre esta base; o consolidar.

---

## Situación actual

Build: ✅ `lake build` exit 0. **0 sorrys reales** y **0 warnings RPP** en los 11 módulos. Los 5 `axiom` de `Axioms.lean` (`imp_intro`, `gen`, `raa`, `or_elim`, `ex_elim`) son meta-reglas de FOL; `ax_p_tfa` en `Block8.lean` es un meta-axioma adicional (TFA). Ninguno es `:= sorry`.

El sistema `Minimal/` cumple su objetivo declarado en [PLANNING.md](PLANNING.md): **34 axiomas matemáticos sin esquema de inducción son suficientes para construir la función de Cantor, las tuplas con proyecciones, las listas con concatenación y pertenencia, las funciones discretas, los primos y la factorización prima** (TFA vía Ax-P).

---

## Eje 1 — Consolidar `Minimal/` ✅ CERRADO (2026-06-06)

Todos los hitos completados:

- [x] **Bloque VII — Funciones discretas**: `Block7.lean` con `IsFunction`, `Functional`, F1/F2/F3 (2026-06-03).
- [x] **Bloque VIII — Primos**: `Block8.lean` con `Dvd`, `IsPrime`, lemas básicos (2026-06-03).
- [x] **Bloque VIII extendido — Factorización**: `pow`, `prod_pairs`, `IsFactorization`, `Ax-P` (TFA). Sistema 30 → **34 axiomas matemáticos** (2026-06-06). Auditoría profunda en [MINIMAL-AXIOMS.md](MINIMAL-AXIOMS.md) §3.4-3.5.
- [x] **Limpieza warnings global**: 411 → 0 warnings RPP, linter `unusedSimpArgs true` global (2026-06-06).
- [x] **Diagnóstico frente Gödel (Nivel A)**: `Minimal/` satisface las hipótesis de Gödel I; relación con TFA y EFA/I∆₀+Exp analizada en [GODEL-STATUS.md](GODEL-STATUS.md) y [MINIMAL-AXIOMS.md](MINIMAL-AXIOMS.md) §5.5.

**Estado de auditoría de axiomas no-induction-bound** (resuelto):

| Axioma | Estado | Comentario |
| --- | --- | --- |
| `ax21_mod2_range` | postulado | requiere inducción (irreducible — analizado en [MINIMAL-AXIOMS.md](MINIMAL-AXIOMS.md) §3.2) |
| `ax24_mod2_of_even` | postulado | requiere inducción sobre `k` (auditado 2026-06-03, irreducible) |
| `ax_C3_concat_assoc` | postulado | requiere inducción sobre `L` (irreducible) |
| `ax_L3_in_concat` | postulado | requiere inducción sobre `L` (irreducible) |
| `ax_pow_zero`, `ax_pow_succ` | postulados | definicionales puros (recursión primitiva base — [MINIMAL-AXIOMS.md](MINIMAL-AXIOMS.md) §3.4.1) |
| `ax_prodp_nil`, `ax_prodp_cons` | postulados | definicionales puros sobre listas (§3.4.2) |
| `ax_p_tfa` (TFA) | meta-axioma | requiere inducción fuerte; pasa a teorema en `Full/` |
| ~~`ax20`, `ax22`, `ax23`, `ax27`, `ax28`~~ | **ELIMINADOS** | derivables sin inducción o redundantes (ver CHANGELOG) |

**Pendientes menores** (no bloquean cierre):

- ✅ ~~Arreglar warning externo `FOL/Theorems/Eq.lean:130`~~ — **RESUELTO 2026-06-06** (eliminado el simp arg `hne` no usado en `substTerm_liftLift`; commit `9888c58` en el repo FOL). Build global con **0 warnings** (incl. FOL externo).
- ✅ ~~Más teoremas sobre `IsFactorization`/`Dvd` usando `ax_p_tfa`~~ — **HECHO 2026-06-06**: +10 teoremas en Block8 (álgebra de `Dvd`: `dvd_trans`, `dvd_mul_right/left`, `dvd_mul_of_dvd_left/right`, `dvd_add`; corolarios TFA: `factorization_exists/unique`, `lt_zero_one`, `factorization_one_eq_nil`). Lema de Euclides y multiplicatividad **fuera de scope** (requieren `prod_pairs_concat` → inducción).

---

## Eje 2 — Módulo `Meta/` (Niveles B y C ✅ 2026-06-06; próximo Nivel D)

**Objetivo**: implementar Fases 18-19 del spec (`TuplasFuncionesYListas.md §BLOQUE VIII`) — Gödelización y autorreferencia. Diagnóstico completo y arquitectura en [GODEL-STATUS.md](GODEL-STATUS.md).

**Decisión 2026-06-06**: `Meta/` arranca **al cerrar `Minimal/`**, no después de `Intermediate/`. Justificación: los niveles B-C (codificación + Dem) no requieren inducción, sólo meta-codificación. El nivel D (teoremas de incompletitud demostrados internamente) sí requiere `Intermediate/` o `Full/`.

### 2.1. Nivel B — `Meta/Godel.lean` (primer hito) ✅ COMPLETADO 2026-06-06

- [x] **Asignación de Gödel** `G : símbolos → ℕ` (Def 27 spec). `inductive Sym` (12 símbolos) + `gNat` (tabla ∀→2, ∃→3, =→10, …, m→111) + `gNat_injective`; `numeral`+`numeral_injective`; `G := numeral ∘ gNat` + `G_injective`.
- [x] **Corner brackets** `⌜·⌝ : List Sym → Term` (Def 28): `encode [] = nil`, `encode (s::S) = cons (G s) (encode S)`; notación scoped `⌜·⌝`.
- [x] **Teorema G1** (inyectividad): `encode_injective` (meta-inyectividad consistency-free, vía `injection` + inducción estructural) + versiones object-level `encode_cons_inj` (usa `cons_inj`, Block6) y `encode_cons_neq_nil`. Ver `GODEL-STATUS.md` §2 sobre la elección meta vs objeto.

**No introduce nuevos axiomas matemáticos** sobre `Minimal/`. Aprovecha `pow` + TFA para codificación primorial alternativa (ver [GODEL-STATUS.md](GODEL-STATUS.md) §3.1).

### 2.2. Nivel C — `Meta/Provability.lean` (segundo hito) ✅ COMPLETADO 2026-06-06

- [x] **Codificación estructural** de Gödel: `formCode : Formula → Term` (+ `termCode`/`termsCode`/`strCode`/`charsCode`), con **inyectividad demostrada** (`formCode_injective`, `termCode_injective`, … vía `injection`, consistency-free).
- [x] Predicado `IsFormula(x)` (Def 29): `∃ φ, x = formCode φ`. + `Provable x` y el teorema real `provable_formCode_iff` (`Provable ⌜φ⌝ ↔ axioms ⊢ φ`).
- [x] Predicado `Dem(d, x)` (Def 30) — **meta-axioma** (codifica árboles de derivación, requiere Nivel D). + **Teo Meta** `dem_iff_provable` (`axioms ⊢ φ ↔ ∃ d, Dem d ⌜φ⌝`), meta-axioma.
- [x] **Lema del punto fijo** (`diagonal_lemma`): `∀ φ, ∃ ψ, ⊢ ψ ⇔ φ[⌜ψ⌝]` — meta-axioma.
- [x] **Sentencia de Gödel** `goedelSentence` := punto fijo de `¬provFormula`; `goedelSentence_fixedpoint` (`⊢ G_Min ⇔ ¬Prov(⌜G_Min⌝)`) demostrado a partir de `diagonal_lemma`. `provFormula`/`provFormula_repr` postulados.

**Meta-axiomas nuevos (5)**: `Dem`, `dem_iff_provable`, `provFormula`, `provFormula_repr`, `diagonal_lemma`. Justificados: la aritmetización de demostraciones y la diagonalización requieren inducción → pasarán a teoremas en el **Nivel D** (`Intermediate/`/`Full/`). Lo demostrado sin postular: toda la codificación + inyectividad + `provable_formCode_iff`.

### 2.3. Nivel D — `Meta/Incompleteness.lean` (requiere `Intermediate/` o `Full/`)

- [ ] **Gödel I**: `Minimal ⊬ G_Min` y `Minimal ⊬ ¬G_Min` (asumiendo consistencia).
- [ ] **Gödel II**: `Minimal ⊬ Con(Minimal)`.

Esto se queda para más adelante; la formalización requiere inducción sobre la complejidad sintáctica de las demostraciones.

---

## ~~Eje 3 — Sistema `Intermediate/`~~ ❌ ELIMINADO (2026-06-11)

**Decisión 2026-06-11**: `Intermediate/` se elimina por **redundancia conceptual**. El sistema con esquema de inducción restringido a Φ finito **es el caso particular** de `Full/` (cualquier instancia inductiva concreta que necesitemos se obtiene postulando sólo la φ pertinente en `Full/`, sin necesidad de un sistema separado). El prototipo `Intermediate/Induction.lean` confirmó que la inducción general no añade fricción técnica sobre la restringida — por lo tanto no hay coste por colapsar los dos niveles.

Todo lo que iba a desarrollarse en `Intermediate/` (derivar ax6, ax7, ax10-12, ax18, ax19, ax21, ax24, ax_C3, ax_L3 como teoremas) **se desarrolla directamente en `Full/`**. Resultados actuales en Full: ax6, ax7, ax10, ax11, ax12, ax18, ax19, **ax21, ax24** ✅ (ver Eje 4).

`Intermediate/Induction.lean` y el directorio `Intermediate/` quedan **borrados** del repositorio.

---

## Eje 4 — Sistema `Full/` (EN CURSO — arranque object-level 2026-06-07)

> **✅ `Full/Induction.lean` + `Full/Mod2.lean` + `Full/Lists.lean` (2026-06-07 + 2026-06-11)** — Inducción general como **axioma object-level** (`ax_induction : ⊢ inductionFormula φ`), con codificación **lift-aware** de `φ(σn)`. Composición De Bruijn generalizada (`substFormula_succ_lift_gen` + `step_reduce`). **Derivados como teoremas en forma object-level pura**: ax6 (`add_comm_thm`), ax7 (`add_assoc_ax`), ax10/11/12 (mul algebraicos), ax18 (`lt_irrefl_thm`), ax19 (`lt_trichotomy_thm`), y — **2026-06-11 vía Opción C.2** con axioma extra `ax_mod2_alternation : ∀n, mod2(σn)+mod2(n)=1` — `mod2_range_thm : ⊢ ax21_mod2_range` y `mod2_of_even_thm : ⊢ ax24_mod2_of_even`, y — **2026-06-11 vía meta-axioma `ax_list_induction`** (inducción estructural sobre listas, estilo `imp_intro`/`gen` parametrizado por `φ : Term → Formula`) — `concat_assoc_thm : ⊢ ax_C3_concat_assoc` y `in_concat_thm : ⊢ ax_L3_in_concat`. Lemas auxiliares: `mod2_zero_aux`, `a_plus_one_eq_one`, `eq_congr_mod2`, `eq_congr_cons_right_full`, `eq_congr_concat_left/right`, `eq_subst_in`, `iff_intro` (helper local). **`Intermediate/` eliminado** (caso finito de Full). **Estado**: fragmento aritmético + listas de Minimal totalmente cubierto en Full salvo Ax-P (TFA) y los testigos `ax21`/`ax24`/`ax_C3`/`ax_L3` que ya son teoremas. Siguiente: **Ax-P (TFA, inducción fuerte)**, Gödel Nivel D.

**Objetivo (PLANNING §6.3)**: Axiomas de Peano puros + **esquema de inducción general** sobre todas las fórmulas del lenguaje. Todos los axiomas postulados en `Minimal/` (ax21, ax24, ax_C3, ax_L3) y el meta-axioma `ax_p_tfa` (TFA) se vuelven teoremas. Habilita el **Nivel D** del frente Gödel: Gödel I y II demostrados internamente.

### 4.1. Roadmap de Ax-P / TFA — reencuadre **numerales + representabilidad** (2026-06-11)

**Obstrucción foundational detectada** al intentar F2 meta-nivel: en FOL=, (Muro 1) los existenciales object no dan testigos meta — `ex_elim` sólo concluye `axioms ⊢ C`; y (Muro 2) las disyunciones object (tricotomía) no se eliminan a conclusión meta. Por eso `strong_induction_meta` con case-split **no funciona**, y derivar el `ax_p_tfa` *meta* de Block8 con testigos usables es **equivalente a la maquinaria de representabilidad de Gödel** (no hay atajo).

**Decisión (Opción A, Gödel-aware)**: como Gödel Nivel D necesita representabilidad de todos modos, se construye esa capa una vez y TFA cae como corolario. Se trabaja sobre **numerales** (`numeral n = σⁿ(0)`) con **cómputo meta en ℕ + transferencia** vía homomorfismo. Disuelve los dos muros (lo decisional/constructivo ocurre en ℕ). Reutiliza Peano como cómputo meta.

**Capa de representabilidad (cimientos) — HECHO 2026-06-11**:

- [x] **F1 — Inducción fuerte object** (`Full/StrongInduction.lean`): `strong_induction` derivada de `ax_induction` sin axioma nuevo + `substFormula_liftFormula` + `lt_succ_split`.
- [x] **Numerales** (`Full/Numerals.lean`): `numeral : ℕ → Term` + homomorfismo `numeral_add/mul/pow`, orden `numeral_lt`, separación `numeral_ne`. El puente meta↔object.
- [x] **Cuantificación acotada** (`Full/Bounded.lean`): `le_numeral_split` — `d ≤ numeral n` ⇒ casos finitos `d = numeral i`. Convierte ∀ acotado en análisis finito.
- [x] **Divisibilidad** (`Full/Divisibility.lean`): `numeral_dvd` (meta ∣ → object Dvd) + `divisor_le` (divisor de positivo es ≤).

**Capa de teoría de números — HECHO 2026-06-12**:

- [x] **Primalidad representada** (`Full/Primality.lean`): `isPrime_numeral` — `p` primo (meta, hipótesis `2≤p` + divisores triviales, sin Mathlib) ⇒ `IsPrime (numeral p)`. Vía `divisor_le` + `le_numeral_split` + split anidado sobre el cofactor.
- [x] **División con resto** (`Full/Division.lean`): `division_numeral` — `numeral n = numeral(n/d)·numeral d + numeral(n%d)`, `numeral(n%d) < numeral d`. Trivial vía homomorfismo (cómputo `n/d`, `n%d` en ℕ).
- [x] **Factor primo + factorización META** (`Full/PrimeFactor.lean`, ℕ pura sin Mathlib): `exists_prime_factor` (∀ n≥2, ∃ factor primo) + `primeFactorList` (∀ n≥1, ∃ lista plana de primos con producto n), por inducción fuerte (`Nat.strongRecOn`).
- [x] **TFA-existencia transferida** (`Full/Factorization.lean`): `toTerm` (encoding lista de pares `(numeral p, 1)`), `prod_pairs_toTerm` (`⊢ prod_pairs (toTerm ps) =eq numeral (natProd ps)`), y **`tfa_exists_numeral`** — `∀ n≥1, ∃ ps, (∀p∈ps, IsPrimeNat p) ∧ ⊢ prod_pairs (toTerm ps) =eq numeral n`. Autocontenido (sin Peano).

**UNICIDAD + TFA completo — HECHO 2026-06-12**:

- [x] **Unicidad ℕ** (`Full/PrimeFactor.lean`): `euclid` (lema de Euclides vía `Nat.Coprime.dvd_of_dvd_mul_left` de core), `euclid_list`, `prime_dvd_prime_eq`, `natProd_erase`, `count_unique` (misma multiplicidad de cada primo) y **`factorization_perm_unique`** (dos factorizaciones del mismo `n` son permutaciones). Todo ℕ puro, sin Mathlib.
- [x] **TFA completo** (`Full/Factorization.lean`): **`tfa_numeral`** — `∀ n≥1, ∃ ps, (∀p∈ps, IsPrimeNat p) ∧ (⊢ prod_pairs (toTerm ps) =eq numeral n) ∧ (∀ qs factorización de n → ps.Perm qs)`. Existencia object + unicidad ℕ. La unicidad usa hipótesis meta `natProd qs = n` (evita reflejar igualdad de numerales, que necesitaría `Con(axioms)`).

> **`ax_p_tfa` de Block8** (membership object + testigo único object) queda como la forma **idealizada**: no admite discharge constructivo por el Muro 1 (object→meta). `tfa_numeral` es la realización constructiva equivalente para todos los usos reales (numerales/códigos).

### 4.2. Restantes tras TFA

- [x] **Nivel D Gödel — Gödel I (mitad esencial)** (`Meta/Incompleteness.lean`, 2026-06-12): `goedel_first_unprovable` (`Consistent → ⊬ G`), `goedel_first_true`, `incompleteness`. Derivado de D1 + diagonalización del Nivel C.
- [x] **Gödel II** (`goedel_second`, 2026-06-12): `Consistent → ⊬ Con` (`Con := ¬Prov(⌜⊥⌝)`). **Postulando D2/D3**; lema crucial `con_imp_goedelSentence : ⊢ Con⇒G`.
- [x] **Gödel I completo** (`goedel_first_unrefutable`, `goedel_first_undecidable`, 2026-06-13): `⊬ ¬G`, luego `⊬ G ∧ ⊬ ¬G` (G indecidible). Vía **`dne`** (DNE clásica añadida a `FOL/MetaRules.lean`) + reflexión. El obstáculo era el intuicionismo del FOL, no ω-consistencia; Rosser habría sido peor.
- [ ] **Cadena de embeddings**: `FOL⁼ ⊂ Minimal ⊂ Full`.
- [x] **[Deuda menor]** Refactor meta-axiomas FOL → ✅ HECHO 2026-06-12 (`FOL/MetaRules.lean`).

---

## Eje 4.3 — Gödel Nivel D REAL: aritmetización de D1–D3 (EN CURSO, 2026-06-13)

**Motivación**: D1/D2/D3 estaban **postulados** (meta-axiomas opacos). El `provFormula_repr` bicondicional era además imposible por Tarski (rastrea verdad en ℕ). Decisión (Opción A): **aritmetización total** — `demFormula` será una `Formula` Σ₁ concreta con `Dem d x → ⊢ᴴ demFormula[⌜d⌝,⌜x⌝]` demostrada. Plan completo y descomposición en [GODEL-D-ARITHMETIZATION.md](GODEL-D-ARITHMETIZATION.md).

**Reencuadre clave**: el `axioms ⊢` del proyecto usa la **ω-regla** `gen` (premisas infinitas) → no es r.e. → no aritmetizable. Por eso Gödel se aplica a un **cálculo de Hilbert finitario `⊢ᴴ` nuevo, en paralelo**; el ω-sistema queda intacto.

- [x] **Fase 0** (`Meta/Hilbert.lean`): `Prf₀` (Hilbert intuicionista) + `Prf` (clásico). Puentes `prf0_to_derives`/`prf_to_derives : Prf φ → axioms ⊢ φ` usando **solo constructores de `Derives`**; `dne` aparece en **un único punto** (esquema P3), verificado por `#print axioms` (diferencia exacta entre ambos puentes = `{dne}`). `consistentH_of_omega`: la consistencia se hereda.
- [x] **Fase 1** (`Meta/HilbertSeq.lean`): `Rule` (líneas anotadas, evita invertir la sustitución) + verificador decidible `checkProof` + `Derivation`. **Solidez** `derivation_to_prf` + **completitud** `prf_to_derivation` (con `checkAux_append`/`checkAux_shift` para combinar subpruebas) ⟹ `prf_iff_derivation : Prf φ ↔ ∃ rs, Derivation rs φ`. Coding `ruleCode`/`rulesCode` → `Term`, `Dem` **concreto**, `dem_tracks : (∃d, Dem d ⌜φ⌝) ↔ Prf φ` (reemplaza `Dem`/`dem_iff_provable` postulados; solo axiomas estándar de Lean).
- [x] **Fase 2.1** (`Meta/CodeArith.lean`): `numeral_bridge` (Meta.Godel.numeral = Full.numeral) + `gnum_ne`/`gnum_lt`/`gnum_add`/`gnum_mul`/`gnum_refl` (aritmética de códigos re-expuesta de `Full.Numerals`).
- [x] **Fase 2.2 nivel término** (`Meta/SubstArith.lean` + `Minimal/Axioms.lean`): funciones object `varc`/`funcc`/`substtc`/`substtsc` y sus ecuaciones recursivas **integradas en `Minimal.axioms`** (re-derivadas como teoremas vía `ax`+`spec`; `forall_4` requirió el lema de triple lift `substTerm_liftLiftLift`). `substTerm_arith`/`substTerms_arith` (cómputo `⊢ substtc ⌜v⌝ ⌜s⌝ ⌜t⌝ = ⌜substTerm v s t⌝`) por inducción meta mutua. **`#print axioms substTerm_arith` = solo axiomas estándar de Lean** (0 postulados nuevos).
- [x] **Fase 2.2 nivel fórmula** (`Meta/SubstArith.lean` + `Minimal/Axioms.lean`): `liftc`/`liftsc` (lift aritmetizado) + `substfc` con los 8 constructores de código de fórmula (`botc`..`exc`); 13 ecuaciones recursivas más en `Minimal.axioms` (re-derivadas como teoremas). `liftTerm_arith` + `substFormula_arith` (binders ∀/∃ con `succ`-nivel y `liftc zero`-substituyendo, vía congruencias de `cons` y `congr_substfc_arg2`). `#print axioms substFormula_arith` = solo Lean estándar.
- [x] **Fase 2.3** (`Meta/StepArith.lean`): reconocimiento de instancias de axioma — `q1/q2/leibniz_concl_code` (esquemas de sustitución vía `substFormula_arith`); los proposicionales son definicionales.
- [x] **Fase 2.4** (`Meta/CheckArith.lean` + `Minimal/Axioms`): `numeralM`, extractores `carc`/`cdrc`; **`validProofFn`** + `forall_5` + 17 ecuaciones del verificador (params directos; MP/Gen condicionados por `In`) + 17 step lemmas `vpf_*` + lema 4-lift `substTerm_liftLiftLiftLift`; **`provFormulaC`** (demostrabilidad Σ₁) + `provCodeC`. **Pendiente regla `thy`**: nudo de capas (`formCode`/Meta vs `Minimal.axioms`); plan `formCode` a nivel Minimal vía `numeralM`.
- [x] **Fase 2.4-thy + soundness de `thy`** (`Minimal/Axioms` + `Meta/CheckArith`): verificador completo (18 reglas). `thy` recorre `coreAxioms` y es condicional a `In c axiomsCodeT` (`provCodeC` fiel). `formCodeM` + clausura De Bruijn estructural (numerales gigantes de símbolos Unicode).
- [x] **Fase 2.5** (`Meta/Representability.lean`): representabilidad positiva `repr_pos : Prf φ → axioms ⊢ provCodeC φ` (encoder object a medida `proofCode`/`lineCode` + inducción de seguimiento `vpf_run`). `#print axioms` = estándar.
- [x] **Fase 3 (D1)** (`Meta/Necessitation.lean`): `d1`/`necessitation` (= `repr_pos`) + Gödel I modular `goedel_first_unprovable_real`.
- [x] **Lema diagonal real** (`Meta/Diagonal.lean`): `tcFn`/`tc_arith` + `diag_arith` + **`godelC_fixedpoint : ⊢ G ⇔ ¬provCodeC G`** + **`goedel_first_real : ConsistentOmega → ¬ Prf G`** (sin postulados gödelianos).
- [x] **Fase 2.6 cimiento** (`Meta/CodeDistinct.lean`): aritmética negativa de códigos `formCode_ne` + familia.
- [x] **Fase 5 — regla `ind` INTEGRADA** (`Meta/Induction.lean` + stack): `ind_concl_code` + `Prf.ind`/`Rule.ind`/**`ax_vpf_ind`** sólida + `vpf_ind` + caso ind de `vpf_run`. **Verificador: 19 reglas.** `provCodeC` rastrea **IΣ₁**. `repr_pos`/`vpf_ind` `#print axioms` = estándar; `goedel_first_real` cita además `Full.ax_induction` (honesto: Prf modela IΣ₁).
- **D2/D3 → Gödel II real — rediseño honesto del verificador (EN CURSO, 2026-06-21)**.
  Hallazgo: `validProofFn` (opaca/condicional) sirve para la dirección positiva pero
  **bloquea** la inducción sobre testigos de prueba arbitrarios que D2/D3 exigen. Nuevo
  verificador estructural `runFn` (líneas `cons ⌜concl⌝ justif`, reduce vía `carc`).
  - [x] **R1** (`Meta/ProofChain.lean`): `runFn` + ecuaciones + **compositividad**
    `runFn c (p++s) =eq runFn (runFn c p) s` (inducción con acumulador ∀-object).
  - [x] **R2**: predicados `allIn`/`lineWF`/`premsOf`/`lineOk`/`chainOk` + ecuaciones +
    **monotonía** `In_mono`/`allIn_mono`/`lineOk_mono` (para línea arbitraria).
  - [x] **R3**: `concat_nil_right`, `In_mono_right`, **debilitamiento** `runFn c p =eq c++runFn nil p`,
    **composición** `chainOk c (p++s) ⇔ chainOk c p ∧ chainOk (runFn c p) s`, `chainOk_mono`.
  - [x] **R4 — D1 = `repr_pos'`** (`Meta/Representability2.lean`): `Prf φ → ⊢ provCodeC' φ`.
    Encoder `proofCode'` + `runFn_track` (rule-agnóstico) + `chainOk_track` (19-casos) +
    validez de las 19 reglas (`lineWF`/`premsOf`, fieles). `#print axioms` = solo estándar.
  - [x] **R5 — D2** (`Meta/DerivCond.lean`): `⊢ provCodeC'(A⇒B) ⇒ (provCodeC' A ⇒ provCodeC' B)`
    (`r = p++q++[mp]`, vía `chainOk_concat`/`chainOk_mono`/`runFn_concat`/`runFn_weaken`).
  - [x] **Gödel II — núcleo lógico** (`Meta/GodelTwo.lean`): `con_imp_godel'`/`goedel_second'`
    vía **D2 real** + **D3 postulado** (`axiom d3`) + hipótesis explícitas honestas
    (`fp_bwd` punto fijo, `nec1` necesitación, `hgi` ⊬G ω). Mejora sobre legacy (postulaba D2 y D3).
  - **Camino a Gödel II 100% real** (descubierto al analizar D3):
    - [x] **Refactor `Prf.thy → axioms`** ✅ (2026-06-21): `Prf₀.thy` recorre todo `axioms`
      (core++coding); la teoría razona sobre su propia maquinaria (como IΣ₁). Ancla gigante
      `ax_axiomsCodeT` ELIMINADA, `axiomsCodeT` opaco, nuevo meta-axioma
      `ax_inAxC (a ∈ axioms) : ⊢ In (formCodeM a) axiomsCodeT` (sin término gigante ni
      auto-referencia; sonda validó el lift en un paso). Fixes thy en
      `Hilbert`/`HilbertSeq`/`Representability`/`Representability2`. Build 55 jobs.
    - [x] **Punto fijo real para `provCodeC'`** ✅ (`Meta/DiagonalTwo.lean`): `godelC'`/`godelC'_fixedpoint`
      (`⊢ G' ⇔ ¬provCodeC' G'`, sin postulados) + `goedel_first_real'` (Gödel I real estructural).
    - **HALLAZGO de niveles (2026-06-22)**: Gödel II requiere RE-NIVELAR la cadena HBL a `Prf`
      (no ⊢): `provCodeC'` rastrea la demostrabilidad finitaria `Prf`; `¬⊢G'`/`¬⊢Con'` son FALSOS
      (el ω-sistema es sólido y los prueba). Gödel II correcto = `ConsistentH → ¬ Prf Con'`, vía
      `con_imp` a nivel **Prf**, que necesita:
      - [ ] `repr_pos'_prf : Prf φ → Prf (provCodeC' φ)` (re-derivar `repr_pos'`/`chainOk_track` en `Prf`;
        el refactor `Prf.thy → axioms` lo habilitó).
      - [ ] `d2_prf`, punto fijo en `Prf` (`Prf (G' ⇔ ¬provCodeC' G')`).
      - [ ] `con_imp_prf : Prf (Con' ⇒ G')` → `goedel_second_prf : ConsistentH → ¬ Prf Con'` (D3 postulado a nivel Prf).
      - [ ] **D3 real** (Σ₁-completitud provable, núcleo).
    - [ ] **R6 — D3 real** (Σ₁-completitud provable): `⊢ ∀q. (R(q) ⇒ Prov(⌜R(q)⌝))` por inducción
      OBJECT sobre `q` (internaliza `repr_pos'`/`chainOk_track`) + ∃-intro interno + ex_elim.
      La pieza más grande del proyecto. (NOTA: `d3_of_sigma1` en `Reflection.lean` fue descomposición
      errónea —ex_elim sobre witness opaco—; superada por este plan.)
  - [ ] **R7**: replicar `con_imp_goedelSentence`/`goedel_second` con `provCodeC'`/`godelC` → **Gödel II real** (`⊬ Con`).
- [ ] **⊬¬G real** (reflexión / ω-soundness) + representabilidad **negativa** plena.

> **Integración ✅ (2026-06-13)**: las ecuaciones recursivas de las funciones de coding están ahora en `Minimal.axioms` (extensión definicional conservadora), por lo que `⊢ᴴ` también las tiene (vía `Prf.thy`). Ya no hay `axiom` local en `SubstArith`.

---

## Eje 5 — Más allá (muy largo plazo)

Sobre la base consolidada `Full/`:

1. **Teorías de conjuntos constructivas** (CZF de Aczel) usando listas y funciones como cimiento.
2. **Cardinalidad y números enteros/racionales**.
3. **Análisis constructivo elemental** (sucesiones, límites).

---

## Problemas técnicos recurrentes (referencia)

Heredados del trabajo en `Minimal/`. Útiles para `Intermediate/` y `Full/`.

| Problema | Síntoma | Solución |
| --- | --- | --- |
| `Block2.Γ` vs `Block4_C5.Γ` | `apply` falla con unificación | Usar `exact` (igualdad definitional) |
| `eq_trans` no-estándar | cadena `a=b, b=c` falla | Usar `FOL.derive_eq_trans` |
| `substTerm` bajo binder no reducido | `simp` deja `substTerm 0 t s` | añadir `FOL.substTerm_liftTerm`, `FOL.substTerm_liftLift` al simp set |
| `and_elim_*` ambiguo | error de elaboración | usar `Axioms.and_elim_left/right` |
| `Γ ⊢ t ≤ t'` parsing | `(Γ ⊢ t) ≤ t'` | paréntesis: `Γ ⊢ (t ≤ t')` |
| Implicación bajo `=eq` | `⇒` parsea más fuerte que `=eq` | paréntesis: `(A ⇒ (B =eq C))` |
| Triple `spec` (`forall_3`) | doble lift no se cancela | añadir `← lift_01_eq_00` o `FOL.substTerm_liftLift` |
| Caché de `lake build` | "Replayed" oculta cambios sin compilar | `lake clean && lake build` cuando hay dudas |

---

**Author**: Julián Calderón Almendros

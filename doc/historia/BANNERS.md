# Banners de «estado real» retirados (histórico)

**Last updated:** 2026-10-21 — ✏️ [ADR‑186](../../DECISIONS.md) (T29): los de `doc/REFERENCE-Incompleteness.md`, al final. Antes, 2026-10-16 — los banners apilados de siete documentos, trasladados TAL CUAL ([ADR‑142](../../DECISIONS.md), T33). La fuente única del estado es el banner de `TEOREMAS-E-HIPOTESIS.md`. Las anclas `(#adr-…)` y los enlaces relativos de dentro son los de su documento de origen, en la raíz.

## `README.md` — sus líneas 3–81, retiradas el 2026-10-16

> ## 🏁🏁 ESTADO REAL — 2026‑10‑05 · `master` · **`ConsistentH` es un TEOREMA del build: Gödel I y II sin hipótesis DENTRO de Lean** ([ADR‑120](DECISIONS.md)) · la consistencia es **RELATIVA a Lean** ([ADR‑138](DECISIONS.md))
>
> Un modelo de los **142** axiomas (`MNV V₀`: `Meta/ModeloCodigo.lean`, `Meta/ModeloEstandar.lean`,
> `Meta/ModeloCodificacion.lean`) y la solidez de `Prf` en todo modelo estándar (`prf_sound`, `Meta/SolidezPrf.lean`)
> dan `consistencia : ConsistentH`; con ella, `goedel_I : ¬ Prf godelCN` y `goedel_II : ¬ Prf consistencyFormula'`
> (`Meta/Consistencia.lean`), con footprint los tres de Lean. 🏁🏁 Y desde ADR‑121, **Gödel I ENTERO**:
> `goedel_I_neg : ¬ Prf ¬godelCN` (`Meta/SolidezVerificador.lean`, por la solidez del verificador en el modelo), y
> **Tarski** (`Meta/TarskiPrf.lean`); y `G` y `Con` son VERDADERAS en el modelo (E10). ⚠️ Lo que NO dice: Rosser (⬜).
>
> ✏️ *(2026‑10‑16, [ADR‑138](DECISIONS.md))* **Consistencia RELATIVA, no absoluta.** `consistencia` es una prueba
> EN LEAN; lo que garantiza fuera de Lean es PRA ⊢ Con(Lean) → Con(T_Prf), si el núcleo implementa bien esa
> teoría. No puede ser absoluta: `T_Prf` contiene a PA y, por Gödel II, ninguna teoría contenida en ella demuestra su
> consistencia. «Sin hipótesis» quiere decir sin hipótesis dentro de Lean; la que queda, Con(Lean), Lean no la puede
> descargar (Gödel II, aplicado a Lean). Vale igual para `goedel_I`, `goedel_II`, `goedel_I_neg` y `tarski`, que
> implican `ConsistentH`. Los condicionales (`goedel_first_prf`, `goedel_second_prf`, clase (i)) no pasan por el
> modelo; que para ellos baste una metateoría débil es lo esperable, y no está medido.
> [TEOREMAS-E-HIPOTESIS.md](TEOREMAS-E-HIPOTESIS.md) §4.
>
> 🗓️ *Lo que sigue es el estado del 2026‑10‑04, como registro: su «CONDICIONALES … no hay modelo» dejó de valer.*

> ## ESTADO REAL — 2026‑10‑04 · `master` · 🏁 **F1 reparado: Gödel I/II sobre `Prf` dependen sólo de `ConsistentH`** ([ADR‑117](DECISIONS.md))
>
> `axiomsCodeT` queda anclado por un axioma objeto DIAGONAL (L2‑3): `axioms` = **142** = los 141 de siempre
> (`axiomsBase`) y `ax_axiomsCodeT_def`, el último. El ancla de antes, la hipótesis de clase `AnclaEq`, es hoy
> el teorema `prf_ancla` (la clase se retiró con ADR‑118), y `goedel_first_prf` y `goedel_second_prf` ya no la llevan:
> su footprint sigue siendo los tres de Lean, y **F1 ya no los hace vacuos**. ⚠️ Siguen siendo **CONDICIONALES**:
> `ConsistentH` sólo vale si los 142 axiomas son consistentes, y no hay modelo; y `⊬¬G` sigue sin existir en
> ningún cálculo (irá por Rosser, sobre `Prf`).
>
> ### 2026‑10‑02 · 🗑️ **la capa `⊢` RETIRADA** ([ADR‑115](DECISIONS.md)) · ⛔ **Gödel I/II sobre `Prf`: VACUOS** por `[AnclaEq]` hasta ADR‑117 (F1, [ADR‑114](DECISIONS.md))
>
> RPP ya no usa `⊢` (`Derives`): **cinco de sus siete postulados son falsos** —las cuatro meta‑reglas de FOL
> (`imp_intro`, `raa`, `or_elim`, `ex_elim`) y el `axiom` `ax_list_induction` de RPP (retirado) se **refutan sin
> usarlos** (`sondeos/MetaReglasRefutables.lean`, compilado)—; los otros dos, también retirados (`ax_induction_prim`,
> `ax_axiomsCodeT_eq`, retirado con ellos), no se midieron. Se borraron **27 módulos**
> (`Minimal/Theorems/Block1–8`, ocho de `Full/`, nueve de `Meta/`) y **633 declaraciones**; la cadena
> de Gödel sobre `Prf` no usaba ninguna (medido por cierre de dependencias) y compila igual. RPP queda
> con **0 `axiom` de Lean**.
> ⛔ **Lo que NO arregla** *(hasta ADR‑117, 2026‑10‑04)*: `goedel_first_prf` y `goedel_second_prf` llevan la clase
> `[AnclaEq]`, y `AnclaEq` **da `Prf ⊥`** (F1, [ADR‑114](DECISIONS.md), `sondeos/AnclaEqInconsistente.lean`) ⇒ hoy
> los dos teoremas son **VACUOS**. Repararlo (L2‑3: anclar `axiomsCodeT` por punto fijo) es lo siguiente.
>
> ### 🗄️ Registro — el «ESTADO REAL» del 2026‑09‑11
>
> Titulaba «CADENA DE GÖDEL FINITARIA (Gödel I y II sobre `Prf`, hipótesis mínima `ConsistentH`, un solo
> axioma en el footprint) · `axioms ⊢` es COMPLETO». Lo de la hipótesis mínima y el solo axioma dejó de ser
> cierto con ADR‑026 (el ancla pasó a la firma como `[AnclaEq]`; lo primero vuelve a serlo desde ADR‑117), y `⊢`
> ya no está en RPP. Se conserva:
>
> Estado autoritativo: **[NEXT-STEPS.md](NEXT-STEPS.md)** → **[CURRENT-STATUS-PROJECT.md](CURRENT-STATUS-PROJECT.md)**
> (⚠️ `PLAN-FRENTE-A.md` ya **no** es autoritativo: su pregunta —«¿vuelve la capa rastreada?»— está **contestada** desde el 2026‑08‑23)
> → [cuarentena/README.md](cuarentena/README.md) → [sondeos/README.md](sondeos/README.md).
> Catálogo de módulos y proyección: **[REFERENCE.md](REFERENCE.md)** §1 →
> [doc/REFERENCE-Incompleteness.md](doc/REFERENCE-Incompleteness.md) §3.24–§3.32.
>
> **Build 129 jobs · 0 errores · 0 sorrys · Lean v4.31.0.**
> *(Cifras medidas el 2026-10-02, tras retirar la capa `⊢`: ADR-115; jobs, módulos, `axiom` y `sorry`, re‑medidos el 2026-10-04 con ADR-117, sin cambio; 129 jobs y 112 módulos desde el 2026-10-05, con `Minimal/SymLit.lean` (D7, ADR-129). En línea aparte para que `[A]` las compruebe: una línea con fecha ISO cuenta como registro y `[A]` la exime.)*
> **112 módulos activos** (Minimal 2 + Meta 107 + Full 3) **+ 0 en `cuarentena/` + 92 en `sondeos/`.**
> **0 `axiom` de Lean · 142 axiomas objeto** en `axioms` (los 141 de `axiomsBase` más el ancla, ADR‑117; `axioms_len`).
>
> ### Reparada la inconsistencia conocida (ADR-012/013)
>
> * `ax_tc_cons` **RETIRADO** de `axioms` (hacía la teoría **inconsistente**). El `def` sigue en
>   `Minimal/Axioms.lean:827` pero **fuera de las listas** — es una definición muerta.
> * **`goedel_first_real'`, `godelC'_fixedpoint` y `goedel_first_undecidable_real'` YA NO EXISTEN.**
>   Gödel I es hoy **`goedel_first_numeral`** (`Meta/DiagonalNumeral.lean`), sobre la sentencia 🗑️ *(lo que esta línea cita de `⊢` quedó retirado con esa capa, ADR-115)*
>   **numeral** `godelCN`.
> * **`cuarentena/` VACÍA** (0 módulos): D3 y Gödel II están **repatriados a la cadena activa**.
>   ⚠️ Que estén dentro del build no los hace probados — ver la fila de D3 y `NEXT-STEPS.md`.
> * ⚠️ **NO es una prueba de consistencia**: se retiró la inconsistencia **conocida y localizada**.
>
> ### La ESCALERA (a.2) COMPLETA — 4 de 4
>
> `pcc_eval_add` → `pcc_eval_mul` → `div2` → **`pcc_dot_cons`** (`Meta/DotConsPrf.lean`): la
> Σ₁‑completitud **internalizada** para argumentos ABSTRACTOS. Rédito verificado en
> `archivo/sondeos-2026-10:sondeos/CarcPayoff.lean`. ▶ **PASO 1 EJECUTADO (2026-08-23)**: `EvalListPrf` repatriado, y con él
> **6 módulos más en cascada** — cuarentena **21 → 12**. ▶ **PASO 2 EJECUTADO**: `EvalNthcPrf` + `EvalCarcNthcPrf` de vuelta (cuarentena 14 → 12). ▶ **PASO 3 EJECUTADO**: `D3InDotPrf` de vuelta ⇒ **D3 reducida otra vez a UN SOLO lema**. ▶ **PASOS 4‑5 EJECUTADOS**: `LineWFTrackedPrf` y el **KIT** (`CodeCtorKit`) en producción. **LA CUARENTENA ESTÁ VACÍA.**
>
> ⚠️ **`⊬¬G` sigue SIN cerrar** en la cadena real (falta `NegVerifier`); es frente independiente.

## `REFERENCE.md` — sus líneas 3–86, retiradas el 2026-10-16

> ## 🏁🏁 ESTADO REAL — 2026‑10‑05 · `master` · **`ConsistentH` es un TEOREMA del build: Gödel I y II sin hipótesis DENTRO de Lean** ([ADR‑120](DECISIONS.md)) · la consistencia es **RELATIVA a Lean** ([ADR‑138](DECISIONS.md))
>
> Un modelo de los **142** axiomas (`MNV V₀`: `Meta/ModeloCodigo.lean`, `Meta/ModeloEstandar.lean`,
> `Meta/ModeloCodificacion.lean`) y la solidez de `Prf` en todo modelo estándar (`prf_sound`, `Meta/SolidezPrf.lean`)
> dan `consistencia : ConsistentH`; con ella, `goedel_I : ¬ Prf godelCN` y `goedel_II : ¬ Prf consistencyFormula'`
> (`Meta/Consistencia.lean`), con footprint los tres de Lean. 🏁 Y desde ADR‑121, Gödel I ENTERO (`goedel_I_neg`),
> E10 (`G` y `Con` verdaderas en el modelo) y Tarski. ⚠️ Lo que NO dice: Rosser (⬜).
>
> ✏️ *(2026‑10‑16, [ADR‑138](DECISIONS.md))* **Consistencia RELATIVA, no absoluta.** `consistencia` es una prueba
> EN LEAN; lo que garantiza fuera de Lean es PRA ⊢ Con(Lean) → Con(T_Prf), si el núcleo implementa bien esa
> teoría. No puede ser absoluta: `T_Prf` contiene a PA y, por Gödel II, ninguna teoría contenida en ella demuestra su
> consistencia. «Sin hipótesis» quiere decir sin hipótesis dentro de Lean; la que queda, Con(Lean), Lean no la puede
> descargar (Gödel II, aplicado a Lean). Vale igual para `goedel_I`, `goedel_II`, `goedel_I_neg` y `tarski`, que
> implican `ConsistentH`. Los condicionales (`goedel_first_prf`, `goedel_second_prf`, clase (i)) no pasan por el
> modelo; que para ellos baste una metateoría débil es lo esperable, y no está medido.
> [TEOREMAS-E-HIPOTESIS.md](TEOREMAS-E-HIPOTESIS.md) §4.
>
> 🏁 **D7 ejecutada (ADR‑129, 2026‑10‑05)**: los símbolos de FOL son `List Char` (antes `String`), en FOL y en RPP; los
> literales de varios caracteres se escriben `sym!"…"` (`Minimal/SymLit.lean`). Ningún valor cambia (`codeNat`, `V₀`,
> `godelCN`, el ancla); 44 filas de `check-footprints` pierden `Classical.choice`, ninguna de los titulares de Gödel
> (su `choice` es el de la solidez clásica, `prf_sound`). ✏️ *(2026‑10‑05, [ADR‑131](DECISIONS.md))*: la causa era una INFERENCIA, y es falsa: MEDIDO (`sondeos/ChoiceFrontera.lean`), 168 de las 182 filas con `Classical.choice` no pasan por `prf_sound`; 158 lo reciben sólo de dos cancelaciones de lift (`SubstArith.substTerm_liftLiftLift` y `…LiftLiftLift`), entre ellas `goedel_first_prf`, `goedel_second_prf` y `prf_tarski`.
>
> 🗓️ *Lo que sigue es el estado del 2026‑10‑04, como registro: su «CONDICIONALES … no hay modelo» dejó de valer.*

> ## ESTADO REAL — 2026‑10‑04 · `master` · 🏁 **F1 reparado: Gödel I/II sobre `Prf` dependen sólo de `ConsistentH`** ([ADR‑117](DECISIONS.md)) · 🗑️ **la capa `⊢` RETIRADA** ([ADR‑115](DECISIONS.md))
>
> RPP ya no usa `⊢` (`Derives`): **cinco de sus siete postulados son falsos** —las cuatro meta‑reglas de FOL
> (`imp_intro`, `raa`, `or_elim`, `ex_elim`) y el `axiom` `ax_list_induction` de RPP (retirado) se **refutan sin
> usarlos** (`sondeos/MetaReglasRefutables.lean`, compilado)—; los otros dos, también retirados (`ax_induction_prim`,
> `ax_axiomsCodeT_eq`, retirado con ellos), no se midieron. Se borraron **27 módulos**
> (`Minimal/Theorems/Block1–8`, ocho de `Full/`, nueve de `Meta/`) y **633 declaraciones**; la cadena
> de Gödel sobre `Prf` no usaba ninguna (medido por cierre de dependencias) y compila igual. RPP queda
> con **0 `axiom` de Lean**.
> ⛔ **Lo que NO arreglaba** (hasta ADR‑117, 2026‑10‑04): `goedel_first_prf` y `goedel_second_prf` llevaban la
> clase `[AnclaEq]`, y `AnclaEq` **daba `Prf ⊥`** (F1, [ADR‑114](DECISIONS.md), `sondeos/AnclaEqInconsistente.lean`)
> ⇒ los dos teoremas eran **VACUOS**. Repararlo (L2‑3: anclar `axiomsCodeT` por punto fijo) era lo siguiente.
>
> 🏁 **ADR‑117 (2026‑10‑04) · F1 reparado.** `axiomsCodeT` lo ancla un axioma DIAGONAL, `ax_axiomsCodeT_def`, el
> último de los **142** de `axioms` (los 141 de `axiomsBase` y él); el ancla de antes es el TEOREMA `prf_ancla`, y
> la clase `AnclaEq` se retiró (ADR‑118). `goedel_first_prf`/`goedel_second_prf (hcon : ConsistentH)` ya no
> llevan `[AnclaEq]`, y su footprint es el de los tres axiomas de Lean. ⚠️ Siguen siendo **CONDICIONALES**:
> `ConsistentH` sólo vale si los 142 son consistentes, y no hay modelo; `⊬¬G` sigue sin existir en ningún cálculo.
>
> ### 🗄️ Registro — el «ESTADO REAL» del 2026‑09‑11
>
> Titulaba «CADENA DE GÖDEL FINITARIA (Gödel I y II sobre `Prf`, hipótesis mínima `ConsistentH`, un solo
> axioma en el footprint) · `axioms ⊢` es COMPLETO». Lo de la hipótesis mínima y el solo axioma dejó de ser
> cierto con ADR‑026 (el ancla pasó a la firma como `[AnclaEq]`; la hipótesis mínima volvió con ADR‑117, el
> 2026‑10‑04, ya sin ningún axioma del proyecto en el footprint), y `⊢` ya no está en RPP. Se conserva:
>
> **Build 129 jobs · 0 errores · 0 sorrys · Lean v4.31.0.**
> *(Cifras medidas el 2026-10-02, tras retirar la capa `⊢`: ADR-115; jobs, módulos, `axiom` y `sorry`, re‑medidos el 2026-10-04 con ADR-117, sin cambio; 129 jobs y 112 módulos desde el 2026-10-05, con `Minimal/SymLit.lean` (D7, ADR-129). En línea aparte para que `[A]` las compruebe: una línea con fecha ISO cuenta como registro y `[A]` la exime.)*
> **112 módulos activos** (Minimal 2 + Meta 107 + Full 3) **+ 0 en `cuarentena/`** (fuera del build)
> **+ 92 en `sondeos/`** (experimentos, fuera del build; no todos compilan hoy: 39 de 92, [ADR‑134](DECISIONS.md); la última pasada entera, la de D7, [ADR‑129](DECISIONS.md)).
> **0 `axiom` de Lean** ([`AXIOMS.md`](AXIOMS.md)) · **142 axiomas objeto** en `axioms` (los 141 de `axiomsBase`
> y el ancla diagonal, ADR‑117).
>
> ### ✅ La inconsistencia conocida está REPARADA ([ADR‑012](DECISIONS.md))
>
> `ax_tc_cons` **retirado** de `axioms`: obligaba a `tcFn` a recurrir a la vez sobre estructura
> NUMERAL y sobre estructura de CÓDIGO — imposible, porque en ℕ el mismo valor es ambas cosas
> (`cons 0 nil = 2 = σσ0`). Los códigos de Gödel se escriben ahora como **NUMERALES**.
>
> * **`goedel_first_real'`, `godelC'_fixedpoint` y `goedel_first_undecidable_real'` YA NO EXISTEN.**
>   Gödel I es hoy **`goedel_first_numeral`** (`Meta/DiagonalNumeral.lean`), sobre `godelCN`. 🗑️ *(lo que esta línea cita de `⊢` quedó retirado con esa capa, ADR-115)*
> * **21 módulos a `cuarentena/`** ([ADR‑013](DECISIONS.md)) — cifra histórica del momento de la
>   reparación; hoy la cuarentena está **VACÍA** (§1.6). Sus teoremas eran formalmente correctos pero **vacuos**.
> * ⚠️ **NO es una prueba de consistencia**: se retiró la inconsistencia **conocida y localizada**.
>
> ### ✅ La ESCALERA (a.2) está COMPLETA — 4 de 4
>
> `pcc_eval_add` → `pcc_eval_mul` → `div2` → **`pcc_dot_cons`** (`Meta/DotConsPrf.lean`): la
> Σ₁‑completitud **internalizada** para argumentos abstractos, que es lo que repatría la cuarentena.
> Rédito verificado en `archivo/sondeos-2026-10:sondeos/CarcPayoff.lean` (`pcc_eval_carc` vuelve). Detalle en
> [Incompletitud §3.24–§3.32](doc/REFERENCE-Incompleteness.md).
>
> ### 🏁🏁 Y desde el 2026‑09‑14 hay un cálculo de FOL⁼ del que SE PUEDE HABLAR
>
> **`Derives₀`** ([ADR‑033](DECISIONS.md)): 21 constructores, **cero habitantes‑axioma** ⇒ **la
> inducción es legítima**. Con él: **`derives0_soundness`**, **`derives0_consistent`** (la primera
> consistencia de un cálculo de FOL⁼ del proyecto) y **`derives0_not_complete`**. Ver §0bis.
>
> **Punto de reanudación:** **[NEXT-STEPS.md](NEXT-STEPS.md)** → **[PLAN-FRENTE-A.md](PLAN-FRENTE-A.md)**
> → [cuarentena/README.md](cuarentena/README.md) → [sondeos/README.md](sondeos/README.md).

## `DEPENDENCIES.md` — sus líneas 3–68, retiradas el 2026-10-16

> ## 🏁🏁 ESTADO REAL — 2026‑10‑05 · `master` · **`ConsistentH` es un TEOREMA del build: Gödel I y II SIN HIPÓTESIS** ([ADR‑120](DECISIONS.md))
>
> Un modelo de los **142** axiomas (`MNV V₀`: `Meta/ModeloCodigo.lean`, `Meta/ModeloEstandar.lean`,
> `Meta/ModeloCodificacion.lean`) y la solidez de `Prf` en todo modelo estándar (`prf_sound`, `Meta/SolidezPrf.lean`)
> dan `consistencia : ConsistentH`; con ella, `goedel_I : ¬ Prf godelCN` y `goedel_II : ¬ Prf consistencyFormula'`
> (`Meta/Consistencia.lean`), con footprint los tres de Lean. 🏁 Y desde ADR‑121, Gödel I ENTERO (`goedel_I_neg`),
> E10 (`G` y `Con` verdaderas en el modelo) y Tarski. ⚠️ Lo que NO dice: Rosser (⬜).
>
> 🗓️ *Lo que sigue es el estado del 2026‑10‑04, como registro: su «CONDICIONALES … no hay modelo» dejó de valer.*

> ## ESTADO REAL — 2026‑10‑04 · `master` · 🏁 **F1 reparado: Gödel I/II sobre `Prf` dependen sólo de `ConsistentH`** ([ADR‑117](DECISIONS.md)) · 🗑️ **la capa `⊢` RETIRADA** ([ADR‑115](DECISIONS.md))
>
> RPP ya no usa `⊢` (`Derives`): **cinco de sus siete postulados son falsos** —las cuatro meta‑reglas de FOL
> (`imp_intro`, `raa`, `or_elim`, `ex_elim`) y el `axiom` `ax_list_induction` de RPP (retirado) se **refutan sin
> usarlos** (`sondeos/MetaReglasRefutables.lean`, compilado)—; los otros dos, también retirados (`ax_induction_prim`,
> `ax_axiomsCodeT_eq`, retirado con ellos), no se midieron. Se borraron **27 módulos**
> (`Minimal/Theorems/Block1–8`, ocho de `Full/`, nueve de `Meta/`) y **633 declaraciones**; la cadena
> de Gödel sobre `Prf` no usaba ninguna (medido por cierre de dependencias) y compila igual. RPP queda
> con **0 `axiom` de Lean**.
> ⛔ **Lo que NO arreglaba** (hasta ADR‑117, 2026‑10‑04): `goedel_first_prf` y `goedel_second_prf` llevaban la
> clase `[AnclaEq]`, y `AnclaEq` **daba `Prf ⊥`** (F1, [ADR‑114](DECISIONS.md), `sondeos/AnclaEqInconsistente.lean`)
> ⇒ los dos teoremas eran **VACUOS**. Repararlo (L2‑3: anclar `axiomsCodeT` por punto fijo) era lo siguiente.
>
> 🏁 **ADR‑117 (2026‑10‑04) · F1 reparado.** `axiomsCodeT` lo ancla un axioma DIAGONAL, `ax_axiomsCodeT_def`, el
> último de los **142** de `axioms` (los 141 de `axiomsBase` y él); el ancla de antes es el TEOREMA `prf_ancla`, y
> la clase `AnclaEq` se retiró (ADR‑118). `goedel_first_prf`/`goedel_second_prf (hcon : ConsistentH)` ya no
> llevan `[AnclaEq]`, y su footprint es el de los tres axiomas de Lean. ⚠️ Siguen siendo **CONDICIONALES**:
> `ConsistentH` sólo vale si los 142 son consistentes, y no hay modelo; `⊬¬G` sigue sin existir en ningún cálculo.
>
> ### 🗄️ Registro — el «ESTADO REAL» del 2026‑09‑11
>
> Titulaba «CADENA DE GÖDEL FINITARIA (Gödel I y II sobre `Prf`, hipótesis mínima `ConsistentH`, un solo
> axioma en el footprint) · `axioms ⊢` es COMPLETO». Lo de la hipótesis mínima y el solo axioma dejó de ser
> cierto con ADR‑026 (el ancla pasó a la firma como `[AnclaEq]`; la hipótesis mínima volvió con ADR‑117, el
> 2026‑10‑04, ya sin ningún axioma del proyecto en el footprint), y `⊢` ya no está en RPP. Se conserva:
>
> Estado autoritativo: **[NEXT-STEPS.md](NEXT-STEPS.md)** → **[CURRENT-STATUS-PROJECT.md](CURRENT-STATUS-PROJECT.md)**
> (⚠️ `PLAN-FRENTE-A.md` ya **no** es autoritativo: su pregunta —«¿vuelve la capa rastreada?»— está **contestada** desde el 2026‑08‑23)
> → [cuarentena/README.md](cuarentena/README.md) → [sondeos/README.md](sondeos/README.md).
> Catálogo de módulos y proyección: **[REFERENCE.md](REFERENCE.md)** §1 →
> [doc/REFERENCE-Incompleteness.md](doc/REFERENCE-Incompleteness.md) §3.24–§3.32.
>
> **Build 129 jobs · 0 errores · 0 sorrys · Lean v4.31.0.**
> *(Cifras medidas el 2026-10-02, tras retirar la capa `⊢`: ADR-115; jobs, módulos, `axiom` y `sorry`, re‑medidos el 2026-10-04 con ADR-117, sin cambio; 129 jobs y 112 módulos desde el 2026-10-05, con `Minimal/SymLit.lean` (D7, ADR-129). En línea aparte para que `[A]` las compruebe: una línea con fecha ISO cuenta como registro y `[A]` la exime.)*
> **112 módulos activos** (Minimal 2 + Meta 107 + Full 3) **+ 0 en `cuarentena/` + 92 en `sondeos/`.**
> **0 `axiom` de Lean · 142 axiomas objeto** en `axioms` (los 141 de `axiomsBase` y el ancla diagonal, ADR‑117).
>
> ### Reparada la inconsistencia conocida (ADR-012/013)
>
> * `ax_tc_cons` **RETIRADO** de `axioms` (hacía la teoría **inconsistente**). El `def` sigue en
>   `Minimal/Axioms.lean:827` pero **fuera de las listas** — es una definición muerta.
> * **`goedel_first_real'`, `godelC'_fixedpoint` y `goedel_first_undecidable_real'` YA NO EXISTEN.**
>   Gödel I es hoy **`goedel_first_numeral`** (`Meta/DiagonalNumeral.lean`), sobre la sentencia 🗑️ *(lo que esta línea cita de `⊢` quedó retirado con esa capa, ADR-115)*
>   **numeral** `godelCN`.
> * **`cuarentena/` VACÍA** (0 módulos): D3 y Gödel II están **repatriados a la cadena activa**.
>   ⚠️ Que estén dentro del build no los hace probados — ver la fila de D3 y `NEXT-STEPS.md`.
> * ⚠️ **NO es una prueba de consistencia**: se retiró la inconsistencia **conocida y localizada**.
>
> ### La ESCALERA (a.2) COMPLETA — 4 de 4
>
> `pcc_eval_add` → `pcc_eval_mul` → `div2` → **`pcc_dot_cons`** (`Meta/DotConsPrf.lean`): la
> Σ₁‑completitud **internalizada** para argumentos ABSTRACTOS. Rédito verificado en
> `archivo/sondeos-2026-10:sondeos/CarcPayoff.lean`. ▶ **PASO 1 EJECUTADO (2026-08-23)**: `EvalListPrf` repatriado, y con él
> **6 módulos más en cascada** — cuarentena **21 → 12**. ▶ **PASO 2 EJECUTADO**: `EvalNthcPrf` + `EvalCarcNthcPrf` de vuelta (cuarentena 14 → 12). ▶ **PASO 3 EJECUTADO**: `D3InDotPrf` de vuelta ⇒ **D3 reducida otra vez a UN SOLO lema**. ▶ **PASOS 4‑5 EJECUTADOS**: `LineWFTrackedPrf` y el **KIT** (`CodeCtorKit`) en producción. **LA CUARENTENA ESTÁ VACÍA.**
>
> ⚠️ **`⊬¬G` sigue SIN cerrar** en la cadena real (falta `NegVerifier`); es frente independiente.

## `GODEL-STATUS.md` — sus líneas 3–72, retiradas el 2026-10-16

> ## 🏁🏁 ESTADO REAL — 2026‑10‑05 · `master` · **`ConsistentH` es un TEOREMA del build: Gödel I y II SIN HIPÓTESIS** ([ADR‑120](DECISIONS.md))
>
> Un modelo de los **142** axiomas (`MNV V₀`: `Meta/ModeloCodigo.lean`, `Meta/ModeloEstandar.lean`,
> `Meta/ModeloCodificacion.lean`) y la solidez de `Prf` en todo modelo estándar (`prf_sound`, `Meta/SolidezPrf.lean`)
> dan `consistencia : ConsistentH`; con ella, `goedel_I : ¬ Prf godelCN` y `goedel_II : ¬ Prf consistencyFormula'`
> (`Meta/Consistencia.lean`), con footprint los tres de Lean. 🏁🏁 Y desde ADR‑121, **Gödel I ENTERO**:
> `goedel_I_neg : ¬ Prf ¬godelCN` (`Meta/SolidezVerificador.lean`, por la solidez del verificador en el modelo), y
> **Tarski** (`Meta/TarskiPrf.lean`); y `G` y `Con` son VERDADERAS en el modelo (E10). ⚠️ Lo que NO dice: Rosser (⬜).
>
> 🗓️ *Lo que sigue es el estado del 2026‑10‑04, como registro: su «CONDICIONALES … no hay modelo» dejó de valer.*

> ## ESTADO REAL — 2026‑10‑04 · `master` · 🏁 **F1 reparado: Gödel I/II sobre `Prf` dependen sólo de `ConsistentH`** ([ADR‑117](DECISIONS.md))
>
> `axiomsCodeT` queda anclado por un axioma objeto DIAGONAL (L2‑3): `axioms` = **142** = los 141 de siempre
> (`axiomsBase`) y `ax_axiomsCodeT_def`, el último. El ancla de antes, la hipótesis de clase `AnclaEq`, es hoy
> el teorema `prf_ancla` (la clase se retiró con ADR‑118), y `goedel_first_prf` y `goedel_second_prf` ya no la llevan:
> su footprint sigue siendo los tres de Lean, y **F1 ya no los hace vacuos**. ⚠️ Siguen siendo **CONDICIONALES**:
> `ConsistentH` sólo vale si los 142 axiomas son consistentes, y no hay modelo; y `⊬¬G` sigue sin existir en
> ningún cálculo (irá por Rosser, sobre `Prf`).
>
> ### 2026‑10‑02 · 🗑️ **la capa `⊢` RETIRADA** ([ADR‑115](DECISIONS.md)) · ⛔ **Gödel I/II sobre `Prf`: VACUOS** por `[AnclaEq]` hasta ADR‑117 (F1, [ADR‑114](DECISIONS.md))
>
> RPP ya no usa `⊢` (`Derives`): **cinco de sus siete postulados son falsos** —las cuatro meta‑reglas de FOL
> (`imp_intro`, `raa`, `or_elim`, `ex_elim`) y el `axiom` `ax_list_induction` de RPP (retirado) se **refutan sin
> usarlos** (`sondeos/MetaReglasRefutables.lean`, compilado)—; los otros dos, también retirados (`ax_induction_prim`,
> `ax_axiomsCodeT_eq`, retirado con ellos), no se midieron. Se borraron **27 módulos**
> (`Minimal/Theorems/Block1–8`, ocho de `Full/`, nueve de `Meta/`) y **633 declaraciones**; la cadena
> de Gödel sobre `Prf` no usaba ninguna (medido por cierre de dependencias) y compila igual. RPP queda
> con **0 `axiom` de Lean**.
> ⛔ **Lo que NO arregla** *(hasta ADR‑117, 2026‑10‑04)*: `goedel_first_prf` y `goedel_second_prf` llevan la clase
> `[AnclaEq]`, y `AnclaEq` **da `Prf ⊥`** (F1, [ADR‑114](DECISIONS.md), `sondeos/AnclaEqInconsistente.lean`) ⇒ hoy
> los dos teoremas son **VACUOS**. Repararlo (L2‑3: anclar `axiomsCodeT` por punto fijo) es lo siguiente.
>
> ### 🗄️ Registro — el «ESTADO REAL» del 2026‑09‑11
>
> Titulaba «CADENA DE GÖDEL FINITARIA (Gödel I y II sobre `Prf`, hipótesis mínima `ConsistentH`, un solo
> axioma en el footprint) · `axioms ⊢` es COMPLETO». Lo de la hipótesis mínima y el solo axioma dejó de ser
> cierto con ADR‑026 (el ancla pasó a la firma como `[AnclaEq]`; lo primero vuelve a serlo desde ADR‑117), y `⊢`
> ya no está en RPP. Se conserva:
>
> Estado autoritativo: **[NEXT-STEPS.md](NEXT-STEPS.md)** → **[CURRENT-STATUS-PROJECT.md](CURRENT-STATUS-PROJECT.md)**
> (⚠️ `PLAN-FRENTE-A.md` ya **no** es autoritativo: su pregunta —«¿vuelve la capa rastreada?»— está **contestada** desde el 2026‑08‑23)
> → [cuarentena/README.md](cuarentena/README.md) → [sondeos/README.md](sondeos/README.md).
> Catálogo de módulos y proyección: **[REFERENCE.md](REFERENCE.md)** §1 →
> [doc/REFERENCE-Incompleteness.md](doc/REFERENCE-Incompleteness.md) §3.24–§3.32.
>
> **Build 129 jobs · 0 errores · 0 sorrys · Lean v4.31.0.**
> *(Cifras medidas el 2026-10-02, tras retirar la capa `⊢`: ADR-115; jobs, módulos, `axiom` y `sorry`, re‑medidos el 2026-10-04 con ADR-117, sin cambio; 129 jobs y 112 módulos desde el 2026-10-05, con `Minimal/SymLit.lean` (D7, ADR-129). En línea aparte para que `[A]` las compruebe: una línea con fecha ISO cuenta como registro y `[A]` la exime.)*
> **112 módulos activos** (Minimal 2 + Meta 107 + Full 3) **+ 0 en `cuarentena/` + 92 en `sondeos/`.**
> **0 `axiom` de Lean · 142 axiomas objeto** en `axioms` (los 141 de `axiomsBase` más el ancla, ADR‑117; `axioms_len`).
>
> ### Reparada la inconsistencia conocida (ADR-012/013)
>
> * `ax_tc_cons` **RETIRADO** de `axioms` (hacía la teoría **inconsistente**). El `def` sigue en
>   `Minimal/Axioms.lean:827` pero **fuera de las listas** — es una definición muerta.
> * **`goedel_first_real'`, `godelC'_fixedpoint` y `goedel_first_undecidable_real'` YA NO EXISTEN.**
>   Gödel I es hoy **`goedel_first_numeral`** (`Meta/DiagonalNumeral.lean`), sobre la sentencia 🗑️ *(lo que esta línea cita de `⊢` quedó retirado con esa capa, ADR-115)*
>   **numeral** `godelCN`.
> * **`cuarentena/` VACÍA** (0 módulos): D3 y Gödel II están **repatriados a la cadena activa**.
>   ⚠️ Que estén dentro del build no los hace probados — ver la fila de D3 y `NEXT-STEPS.md`.
> * ⚠️ **NO es una prueba de consistencia**: se retiró la inconsistencia **conocida y localizada**.
>
> ### La ESCALERA (a.2) COMPLETA — 4 de 4
>
> `pcc_eval_add` → `pcc_eval_mul` → `div2` → **`pcc_dot_cons`** (`Meta/DotConsPrf.lean`): la
> Σ₁‑completitud **internalizada** para argumentos ABSTRACTOS. Rédito verificado en
> `archivo/sondeos-2026-10:sondeos/CarcPayoff.lean`. ▶ **PASO 1 EJECUTADO (2026-08-23)**: `EvalListPrf` repatriado, y con él
> **6 módulos más en cascada** — cuarentena **21 → 12**. ▶ **PASO 2 EJECUTADO**: `EvalNthcPrf` + `EvalCarcNthcPrf` de vuelta (cuarentena 14 → 12). ▶ **PASO 3 EJECUTADO**: `D3InDotPrf` de vuelta ⇒ **D3 reducida otra vez a UN SOLO lema**. ▶ **PASOS 4‑5 EJECUTADOS**: `LineWFTrackedPrf` y el **KIT** (`CodeCtorKit`) en producción. **LA CUARENTENA ESTÁ VACÍA.**
>
> ⚠️ **`⊬¬G` sigue SIN cerrar** en la cadena real (falta `NegVerifier`); es frente independiente.

## `AXIOMS.md` — sus líneas 3–77, retiradas el 2026-10-16

> ## 🏁🏁 ESTADO REAL — 2026‑10‑05 · `master` · **`ConsistentH` es un TEOREMA del build: Gödel I y II sin hipótesis DENTRO de Lean** ([ADR‑120](DECISIONS.md)) · la consistencia es **RELATIVA a Lean** ([ADR‑138](DECISIONS.md))
>
> Un modelo de los **142** axiomas (`MNV V₀`: `Meta/ModeloCodigo.lean`, `Meta/ModeloEstandar.lean`,
> `Meta/ModeloCodificacion.lean`) y la solidez de `Prf` en todo modelo estándar (`prf_sound`, `Meta/SolidezPrf.lean`)
> dan `consistencia : ConsistentH`; con ella, `goedel_I : ¬ Prf godelCN` y `goedel_II : ¬ Prf consistencyFormula'`
> (`Meta/Consistencia.lean`), con footprint los tres de Lean. 🏁 Y desde ADR‑121, Gödel I ENTERO (`goedel_I_neg`),
> E10 (`G` y `Con` verdaderas en el modelo) y Tarski. ⚠️ Lo que NO dice: Rosser (⬜).
>
> ✏️ *(2026‑10‑16, [ADR‑138](DECISIONS.md))* **Consistencia RELATIVA, no absoluta.** `consistencia` es una prueba
> EN LEAN; lo que garantiza fuera de Lean es PRA ⊢ Con(Lean) → Con(T_Prf), si el núcleo implementa bien esa
> teoría. No puede ser absoluta: `T_Prf` contiene a PA y, por Gödel II, ninguna teoría contenida en ella demuestra su
> consistencia. «Sin hipótesis» quiere decir sin hipótesis dentro de Lean; la que queda, Con(Lean), Lean no la puede
> descargar (Gödel II, aplicado a Lean). Vale igual para `goedel_I`, `goedel_II`, `goedel_I_neg` y `tarski`, que
> implican `ConsistentH`. Los condicionales (`goedel_first_prf`, `goedel_second_prf`, clase (i)) no pasan por el
> modelo; que para ellos baste una metateoría débil es lo esperable, y no está medido. §0.2 y
> [TEOREMAS-E-HIPOTESIS.md](TEOREMAS-E-HIPOTESIS.md) §4.
>
> 🗓️ *Lo que sigue es el estado del 2026‑10‑04, como registro: su «CONDICIONALES … no hay modelo» dejó de valer.*

> ## ESTADO REAL — 2026‑10‑04 · `master` · 🏁 **F1 reparado: Gödel I/II sobre `Prf` dependen sólo de `ConsistentH`** ([ADR‑117](DECISIONS.md)) · 🗑️ **la capa `⊢` RETIRADA** ([ADR‑115](DECISIONS.md))
>
> RPP ya no usa `⊢` (`Derives`): **cinco de sus siete postulados son falsos** —las cuatro meta‑reglas de FOL
> (`imp_intro`, `raa`, `or_elim`, `ex_elim`) y el `axiom` `ax_list_induction` de RPP (retirado) se **refutan sin
> usarlos** (`sondeos/MetaReglasRefutables.lean`, compilado)—; los otros dos, también retirados (`ax_induction_prim`,
> `ax_axiomsCodeT_eq`, retirado con ellos), no se midieron. Se borraron **27 módulos**
> (`Minimal/Theorems/Block1–8`, ocho de `Full/`, nueve de `Meta/`) y **633 declaraciones**; la cadena
> de Gödel sobre `Prf` no usaba ninguna (medido por cierre de dependencias) y compila igual. RPP queda
> con **0 `axiom` de Lean**.
> ⛔ **Lo que NO arreglaba** (hasta ADR‑117, 2026‑10‑04): `goedel_first_prf` y `goedel_second_prf` llevaban la
> clase `[AnclaEq]`, y `AnclaEq` **daba `Prf ⊥`** (F1, [ADR‑114](DECISIONS.md), `sondeos/AnclaEqInconsistente.lean`)
> ⇒ los dos teoremas eran **VACUOS**. Repararlo (L2‑3: anclar `axiomsCodeT` por punto fijo) era lo siguiente.
>
> 🏁 **ADR‑117 (2026‑10‑04) · F1 reparado.** `axiomsCodeT` lo ancla un axioma DIAGONAL, `ax_axiomsCodeT_def`, el
> último de los **142** de `axioms` (los 141 de `axiomsBase` y él); el ancla de antes es el TEOREMA `prf_ancla`, y
> la clase `AnclaEq` se retiró (ADR‑118). `goedel_first_prf`/`goedel_second_prf (hcon : ConsistentH)` ya no
> llevan `[AnclaEq]`, y su footprint es el de los tres axiomas de Lean. ⚠️ Siguen siendo **CONDICIONALES**:
> `ConsistentH` sólo vale si los 142 son consistentes, y no hay modelo; `⊬¬G` sigue sin existir en ningún cálculo.
>
> ### 🗄️ Registro — el «ESTADO REAL» del 2026‑09‑11
>
> Titulaba «CADENA DE GÖDEL FINITARIA (Gödel I y II sobre `Prf`, hipótesis mínima `ConsistentH`, un solo
> axioma en el footprint) · `axioms ⊢` es COMPLETO». Lo de la hipótesis mínima y el solo axioma dejó de ser
> cierto con ADR‑026 (el ancla pasó a la firma como `[AnclaEq]`; la hipótesis mínima volvió con ADR‑117, el
> 2026‑10‑04, ya sin ningún axioma del proyecto en el footprint), y `⊢` ya no está en RPP. Se conserva:
>
> Estado autoritativo: **[NEXT-STEPS.md](NEXT-STEPS.md)** → **[CURRENT-STATUS-PROJECT.md](CURRENT-STATUS-PROJECT.md)**
> (⚠️ `PLAN-FRENTE-A.md` ya **no** es autoritativo: su pregunta —«¿vuelve la capa rastreada?»— está **contestada** desde el 2026‑08‑23)
> → [cuarentena/README.md](cuarentena/README.md) → [sondeos/README.md](sondeos/README.md).
> Catálogo de módulos y proyección: **[REFERENCE.md](REFERENCE.md)** §1 →
> [doc/REFERENCE-Incompleteness.md](doc/REFERENCE-Incompleteness.md) §3.24–§3.32.
>
> **Build 129 jobs · 0 errores · 0 sorrys · Lean v4.31.0.**
> *(Cifras medidas el 2026-10-02, tras retirar la capa `⊢`: ADR-115; jobs, módulos, `axiom` y `sorry`, re‑medidos el 2026-10-04 con ADR-117, sin cambio; 129 jobs y 112 módulos desde el 2026-10-05, con `Minimal/SymLit.lean` (D7, ADR-129). En línea aparte para que `[A]` las compruebe: una línea con fecha ISO cuenta como registro y `[A]` la exime.)*
> **112 módulos activos** (Minimal 2 + Meta 107 + Full 3) **+ 0 en `cuarentena/` + 92 en `sondeos/`.**
> **0 `axiom` de Lean · 142 axiomas objeto** en `axioms` (los 141 de `axiomsBase` y el ancla diagonal, ADR‑117).
>
> ### Reparada la inconsistencia conocida (ADR-012/013)
>
> * `ax_tc_cons` **RETIRADO** de `axioms` (hacía la teoría **inconsistente**). El `def` sigue en
>   `Minimal/Axioms.lean:827` pero **fuera de las listas** — es una definición muerta.
> * **`goedel_first_real'`, `godelC'_fixedpoint` y `goedel_first_undecidable_real'` YA NO EXISTEN.**
>   Gödel I es hoy **`goedel_first_numeral`** (`Meta/DiagonalNumeral.lean`), sobre la sentencia 🗑️ *(lo que esta línea cita de `⊢` quedó retirado con esa capa, ADR-115)*
>   **numeral** `godelCN`.
> * **`cuarentena/` VACÍA** (0 módulos): D3 y Gödel II están **repatriados a la cadena activa**.
>   ⚠️ Que estén dentro del build no los hace probados — ver la fila de D3 y `NEXT-STEPS.md`.
> * ⚠️ **NO es una prueba de consistencia**: se retiró la inconsistencia **conocida y localizada**.
>
> ### La ESCALERA (a.2) COMPLETA — 4 de 4
>
> `pcc_eval_add` → `pcc_eval_mul` → `div2` → **`pcc_dot_cons`** (`Meta/DotConsPrf.lean`): la
> Σ₁‑completitud **internalizada** para argumentos ABSTRACTOS. Rédito verificado en
> `archivo/sondeos-2026-10:sondeos/CarcPayoff.lean`. ▶ **PASO 1 EJECUTADO (2026-08-23)**: `EvalListPrf` repatriado, y con él
> **6 módulos más en cascada** — cuarentena **21 → 12**. ▶ **PASO 2 EJECUTADO**: `EvalNthcPrf` + `EvalCarcNthcPrf` de vuelta (cuarentena 14 → 12). ▶ **PASO 3 EJECUTADO**: `D3InDotPrf` de vuelta ⇒ **D3 reducida otra vez a UN SOLO lema**. ▶ **PASOS 4‑5 EJECUTADOS**: `LineWFTrackedPrf` y el **KIT** (`CodeCtorKit`) en producción. **LA CUARENTENA ESTÁ VACÍA.**
>
> ⚠️ **`⊬¬G` sigue SIN cerrar** en la cadena real (falta `NegVerifier`); es frente independiente.

## `CURRENT-STATUS-PROJECT.md` — sus líneas 3–276, retiradas el 2026-10-16

> ## 🏁🏁 ESTADO REAL — 2026‑10‑05 · `master` · **`ConsistentH` es un TEOREMA del build: Gödel I y II SIN HIPÓTESIS** ([ADR‑120](DECISIONS.md))
>
> Un modelo de los **142** axiomas (`MNV V₀`: `Meta/ModeloCodigo.lean`, `Meta/ModeloEstandar.lean`,
> `Meta/ModeloCodificacion.lean`) y la solidez de `Prf` en todo modelo estándar (`prf_sound`, `Meta/SolidezPrf.lean`)
> dan `consistencia : ConsistentH`; con ella, `goedel_I : ¬ Prf godelCN` y `goedel_II : ¬ Prf consistencyFormula'`
> (`Meta/Consistencia.lean`), con footprint los tres de Lean. 🏁🏁 Y desde ADR‑121, **Gödel I ENTERO**:
> `goedel_I_neg : ¬ Prf ¬godelCN` (`Meta/SolidezVerificador.lean`, por la solidez del verificador en el modelo), y
> **Tarski** (`Meta/TarskiPrf.lean`); y `G` y `Con` son VERDADERAS en el modelo (E10). ⚠️ Lo que NO dice: Rosser (⬜).
>
> 🗓️ *Lo que sigue es el estado del 2026‑10‑04, como registro: su «CONDICIONALES … no hay modelo» dejó de valer.*

> ### 🏁 2026‑10‑04 · F1 reparado ([ADR‑117](DECISIONS.md)) — el ancla es un TEOREMA, y lo que eso NO dice
>
> `axiomsCodeT` queda anclado por un axioma objeto DIAGONAL (L2‑3): `axioms` = **142** = los 141 de siempre
> (`axiomsBase`) y `ax_axiomsCodeT_def`, el último. El ancla de antes, la hipótesis de clase `AnclaEq`, es hoy
> el teorema `prf_ancla` (la clase se retiró con ADR‑118), y `goedel_first_prf` y `goedel_second_prf` ya no la llevan:
> su footprint sigue siendo los tres de Lean, y **F1 ya no los hace vacuos**. ⚠️ **Lo que NO dice**: que
> `ConsistentH` se cumpla —sólo vale si los 142 axiomas son consistentes, y no hay modelo—, ni `⊬¬G`, que sigue
> sin existir en ningún cálculo (irá por Rosser). Del bloque de abajo sigue vigente lo de `⊢`; su «VACUOS», no.

> ### 🗑️ 2026‑10‑02 · la capa `⊢` RETIRADA ([ADR‑115](DECISIONS.md)) — y lo que eso NO arregla
>
> RPP ya no usa `⊢` (`Derives`): **cinco de sus siete postulados son falsos** —las cuatro meta‑reglas de FOL
> (`imp_intro`, `raa`, `or_elim`, `ex_elim`) y el `axiom` `ax_list_induction` de RPP (retirado) se **refutan sin
> usarlos** (`sondeos/MetaReglasRefutables.lean`, compilado)—; los otros dos, también retirados (`ax_induction_prim`,
> `ax_axiomsCodeT_eq`, retirado con ellos), no se midieron. Se borraron **27 módulos**
> (`Minimal/Theorems/Block1–8`, ocho de `Full/`, nueve de `Meta/`) y **633 declaraciones**; la cadena
> de Gödel sobre `Prf` no usaba ninguna (medido por cierre de dependencias) y compila igual. RPP queda
> con **0 `axiom` de Lean**.
> ⛔ **Lo que NO arregla** *(hasta ADR‑117, 2026‑10‑04)*: `goedel_first_prf` y `goedel_second_prf` llevan la clase
> `[AnclaEq]`, y `AnclaEq` **da `Prf ⊥`** (F1, [ADR‑114](DECISIONS.md), `sondeos/AnclaEqInconsistente.lean`) ⇒ hoy
> los dos teoremas son **VACUOS**. Repararlo (L2‑3: anclar `axiomsCodeT` por punto fijo) es lo siguiente.
> Lo que sigue es el estado del 2026‑09‑10c y se conserva como registro.

> ## ESTADO REAL — 2026-09-10c · **`master`** · 🏁 **VÍA C INTEGRADA** (ADR-020) · ✅ **ÁRBOL VERDE** · ✅ **CI VERDE**
>
> 🏁🏁🏁 **D3 ESTÁ EN UNA SOLA OBLIGACIÓN: `hbody`** (§3.58). `d3_prf_of_body_only` la cierra desde
> ahí, y **todo lo demás está probado** —el puente átomo↔forma acotada, la cota, el `∃` acotado, el
> cuerpo del `∀`, el empaquetado, los **dos** `PsiF`, `hmatch`, `hPinv`, `hPsiId` y `hwP`—, con
> footprint igual a la base sancionada.
>
> `hbody` se parte —por `chainOkBPsi_split`, que conecta los dos `PsiF` **por construcción**— en:
>
> `hbody` está **partido por `rfl`** en sus dos mitades (§3.59), con la **composición de los dos
> `substfc`** — el `PsiF` dotado es él mismo un `substfc`, y el resultado tiene **DOS huecos**.
>
> | mitad | estado | depende de |
> |---|---|---|
> | **(a)** reflexión de `lineWF` = `pcc_lineWF_tracked` | ⬜ **5 de 7** reflectores (`modulo_2`) | **`prf_hasWitF_liftfc`** (`ind` 18, `listInd` 20) |
> | **(b)** reflexión de `boundedPremsIn` | ⬜ núcleo probado, falta ensamblar | ⛔ **el análisis por tags de (a)** |
>
> ⛔⛔ **CORREGIDO (§3.59.2)**: aquí se dijo que (b) «no depende de C3» y era «ensamblaje». **Es
> falso.** Su cota lleva `premsOf` **dotado**, y `premsOf` no está definido por recursión sino por
> **21 axiomas, uno por TAG**, con pattern-matching sobre la forma de la línea ⇒ para un argumento
> abstracto **no hay nada que evaluar**. ⇒ **el orden correcto es (a) primero**.
>
> ⛔ Y **`prf_hasWitF_liftfc` es un FRENTE**, medido (§3.60): no existe ni la mitad TÉRMINO a nivel
> arbitrario, y el molde es una inducción de **2 088 líneas**. La deuda está **enunciada**
> (`DEUDA_hasWitF_liftfc`), con su guarda medida — sólo `hasWitF X`, el nivel **libre**.
>
> ### Cómo se llegó, en cuatro tramos (§3.55–§3.58)
>
> | tramo | de → a | la pieza que lo movió |
> |---|---|---|
> | §3.55 | sin medir → **2** | destino abierto y forma fijada por `rfl`; la cota **dentro de `Prov`**; `hPinv` genérico |
> | §3.56 | 2 → **3** ⚠️ | ⛔ el chasis **no era aplicable**: `hPl` era **FALSA** ⇒ el `PsiF` **dotado** |
> | §3.57 | 3 → **2** | `hPsiId`, con la **tercera variante** de la familia |
> | §3.58 | 2 → **1** | `hwP`, transportando el **testigo** por el puente de §3.56 |
>
> 🔑🔑🔑 **Las tres reglas del frente, y las tres son sobre la FORMA:**
> 1. **El destino fija la IMAGEN; el chasis fija la FORMA en que hay que escribirla.** Hacen falta
>    **los dos** cuerpos —el computable, que casa el destino por `rfl`, y el **dotado**, que es el
>    único natural— y por el puente entre ellos, **dentro de `Prov`**, han viajado ya **tres cosas**:
>    la forma (`hmatch`), la prueba (`hbdAll_of_dotted`) y el testigo (`hwP`).
> 2. **El ÍNDICE no es cosmético, y van tres veces.** La familia `substfc_inv_substCodeF` tiene
>    **tres** variantes y **no son intercambiables**: por debajo del hueco el testigo **deja de ser
>    libre**, y un salto de dos o más haría el enunciado **FALSO**.
> 3. ⚠️ **El contador de obligaciones NO mide el progreso**: §3.56 lo **subió** de 2 a 3 y fue el
>    paso más importante de los cuatro — lo que el «2» medía era una cadena que **no cerraba**.
>
> 🔧 **Y el instrumental mentía** (AI‑GUIDE §27.1): `check-sorry.bash` daba **101 falsos positivos**
> —menciones en prosa— donde hay **0** de verdad; `check-doc-sync.bash` daba verde con los cuatro
> controles `[A]` **vacíos**; y la **CI no
> había arrancado nunca** (YAML inválido). Arreglado el 2026‑09‑09, y lo primero que encontró
> fueron **siete documentos autoritativos** con la cifra de jobs obsoleta.
>
> 🏁 **`Build completed successfully (145 jobs)`** (entonces). La enmienda de los 7 esquemas está aplicada y
> **el árbol entero compila con ella**. La rama `via-c-adr020` (20 commits) se **integró en
> `master`** el 2026-09-07 con merge commit `7bc2c8a`, y el build se verificó verde **después** del
> merge, no sólo en la rama.
>
> 🏁 **LA VÍA C, COMPLETA** (§3.38–§3.40):
> * **`prf_hasWit_substtc` y `prf_hasWitF_substfc`** —las dos clausuras, con código y sustituyendo
>   ABSTRACTOS— en `Meta/SubstfcWitnessPrf.lean`, **net-0 puro**.
> * ✅ **① promoción** (sin ciclo de imports; ⛔ ADR-019 **tres veces** al promover).
> * ✅ **② `MpCodePrf`**: los 10 sitios cerrados; la mitad CÓDIGO se paga entera ahí.
> * ✅ **③ propagación**: los **29 módulos** bloqueados, cerrados.
>
> 🏁 **Y después del merge, dos cierres más el mismo día — los dos net-0** (§3.41):
> * **B3.2 · `Meta/EvalSubsttcPrf.lean`** — `pcc_eval_substtc` / `pcc_eval_substtsc` /
>   `pcc_eval_substtc_hasWit`, con `v`, `s`, `t` **ABSTRACTOS**. Era el **prerrequisito de B3.4**.
>   De 154 declaraciones del sondeo entraron **71**: promover fue sobre todo **borrar**.
> * **El chasis de `hGuard` · `Meta/LineWFGuardPrf.lean`**, **net-0 puro**. Mete en el build
>   `hcond_absorbe_extra` —el lema sobre el que se aceptó ADR-020, que vivía en **cinco copias
>   fuera del build**— y ⭐ `hcond_absorbe_cascade`, que **reduce la deuda de los 7 tags a DOS
>   lemas genéricos**, `DEUDA_hGuardT`/`DEUDA_hGuardF`, **enunciados y no postulados**.
>   ⚠️ Corrigió además la descripción de la enmienda: el conjunto extra es una **cascada** de 1–3
>   guardas anidadas a la derecha, no un par — comprobado con **siete `rfl`** contra
>   `Minimal/Axioms.lean` (§3.41.4).
>
> 🏁 ⭐ **2026-09-08 · B3.4 CERRADO: el muro de `substfc` está DENTRO DEL BUILD** (§3.42).
> `Meta/EvalSubstfcPrf.lean` — `pcc_eval_substfc` con `v`,`s`,`f` **abstractos**,
> `pcc_eval_substfc_wit` y el chasis genérico `pcc_eval_substfc_modulo_8`. Footprint = la base
> sancionada. De **806** declaraciones del sondeo entraron **90**: era la **acreción de cinco
> sondeos**, y `ENS` —el trabajo real— sólo dependía de **41** nombres de los otros cuatro
> namespaces, **31 ya en producción**.
> ⭐ Con esto **`hCarc` queda comprado** para C3: el antecedente de `pcc_eval_substfc_wit` es
> literalmente el conjunto extra que ADR-020 metió dentro del `⇔`.
>
> ▶ **2026-09-09b · `pcc_eval_liftfc`: la base, y una medición que REORDENA el plan** (§3.49).
> `Meta/EvalLiftfcPrf.lean` — `liftfcT` (⛔ **definición**, nunca axioma), `targetLiftfc`, los
> controles y la deuda **enunciada, no postulada**. Footprint = sólo los tres axiomas de Lean.
> ⚠️⚠️ **`pcc_eval_liftc` sólo vale a nivel `zero`**, y `ax_liftfc_forall`/`_ex` **suben el
> nivel** ⇒ **A5 no es una generalización opcional: es PRERREQUISITO** de `pcc_eval_liftfc`, y
> por tanto de los cuatro tags que faltan. Orden correcto: **A5 → chasis → los 4 tags**.
> ⚠️ Y es un frente de **escala B3.4**, no de una sesión.
>
> 🏁 **2026-09-09 · C3: TRES de los SIETE reflectores de sustitución, PROBADOS** (§3.48).
> `pcc_lineWF_tracked_q1_imp` (tag 9), `_q2_imp` (10), `_leibniz_imp` (13); net-0 puros.
> ⭐ **Y se ve por qué ADR-020 puso la guarda donde la puso**: las casillas guardadas son
> **exactamente los hijos del nodo `sub`** — la `witF` sobre el cuerpo del `substfc`, la `wit`
> sobre el sustituyendo. La forma de la enmienda, que parecía arbitraria, resulta ser la
> **aridad de los nodos `sub`** de cada árbol.
> ⚠️ Corrige §3.47.5: `PrfH_dotVN` **no** paga la guarda (es pura congruencia); la paga
> `PrfH_tc_objAt`, vía `pcc_eval_substfc_wit`.
> ⬜ Los otros **cuatro** esperan a `pcc_eval_liftfc`, y hasta que estén los siete
> `pcc_lineWF_tracked` **sigue siendo condicional**.
>
> ▶ **2026-09-08f · C3 ARRANCADO: el chasis del árbol con `substfc`** (§3.47).
> `Meta/SubstTreeReflect.lean` — `STree` con nodo `sub`; footprint = sólo los tres axiomas de
> Lean. ⭐ Los árboles de **q1, q2 y leibniz** declarados y **casados por `rfl` con los axiomas
> ENTEROS**, cascada de guardas incluida ⇒ el `∃ C` de §2.1 de `LineWFGuardPrf` queda resuelto
> para tres tags.
> ⚠️ Y un hueco del chasis, tapado: `hcond_absorbe_cascade` reflejaba cada conjunto por
> separado, y el núcleo estructural **no veía las guardas** — que es justo lo que
> `pcc_eval_substfc_wit` pide como antecedente OBJETO. `hcond_absorbe_1/2/3` se las dan.
> ⭐ **Medición que cuantifica el siguiente frente**: `pcc_eval_liftfc` bloquea **4 de los 7**
> reflectores (q3, qconf, ind, listInd); **tres son alcanzables hoy**.
>
> 🏁🏁 **2026-09-08e · C3-F CERRADO: `DEUDA_hGuardF` PROBADA** (§3.46).
> `pcc_hGuardF` + `hGuard_of_slots`: **la cascada de ADR-020 no tiene ninguna obligación
> abierta**. Footprint = la base sancionada, net-0 puro.
> ⭐ Todo el trabajo estaba en el **`∃∃`**: el `∃` EXTERIOR liga `wF` y el INTERIOR `wT`, luego
> los huecos se rellenan **en dos pasadas y a NIVELES DISTINTOS** ⇒ hubo que **abrir el nivel**
> de la keystone. 🔑 Cuando un `∃` se anida, lo que hay que generalizar no es el testigo: es el
> NIVEL.
> ⚠️ **Y lo que esto NO cierra**: C3 sigue abierto. `pcc_lineWF_tracked_modulo_7` pide un
> reflector por tag y hay **14** en el árbol, ninguno de los 7 de sustitución. Pero lo que les
> falta es ya **sólo la condición ESTRUCTURAL**, que es lo que B3.2/B3.4 compraron.
>
> 🏁 **2026-09-08d · C3-F, la mitad cara: `Meta/HasWitFTrackedPrf.lean`** (§3.45, 828 l.,
> net-0 puro). `pcc_wfAllF_trackedC` — `wfAllF` reflejado con los DOS testigos abstractos y la
> cota ya dotada — sobre `pcc_isFormCodeE2_trackedC`, el recorrido de las OCHO cláusulas.
> ⭐ **La regla de §3.44 aplicada ANTES de construir**: siete `example … := rfl` casando la
> imagen con la que `substCodeF` produce. Acertaron todos a la primera.
> ⭐ Y confirmó que lo genérico de C3-T lo era de verdad: `pcc_shape_tree` en el árbol,
> `shapeFCun`/`shapeFCbin` en el tag, `wfAll1DotAtC` **literalmente el mismo término**.
> ⬜ Queda `isFC1` (trivial), el `∃∃` y la fontanería `condD` — todos con la máquina escrita.
>
> 🏁🏁 **2026-09-08c · C3-T CERRADO: `DEUDA_hGuardT` PROBADA** (§3.44).
> `pcc_hGuardT (i n t) (hin : i < n) : DEUDA_hGuardT i n t` en `Meta/HasWitTrackedPrf.lean`,
> footprint = la base sancionada, **net-0 puro**. Con `hGuard_of_deudaF`, la cascada de ADR-020
> queda a la espera de **UNA sola** deuda: `DEUDA_hGuardF`.
> ⚠️ **La corrección que costó el frente entero, y que conviene no repetir**:
> `condD C t = substfc 0 ṫ (formCode C)` **NO admite elegir imagen** — la impone `formCode`, y
> `formCode (shapeUn X k)` es la **ecuación posicional**, no la conjunción de accesores
> (`shapeDot`) que §5 había elegido. Equivalentes en la teoría objeto, **códigos distintos**.
> ⭐ Y la corrección salió **gratis en teoría objeto**: `pcc_tc_objAt` + `PrfH_dotVN` de
> `Meta/CodeTreeReflect.lean` ya reflejaban esa ecuación por inducción sobre el árbol, desde el
> frente de los 14 tags estructurales. `pcc_shape_tree` sólo las compone — y es genérica, luego
> C3-F la hereda.
> ⚠️ **La cota de casilla `i < n` no es un artefacto**: el puente `(nthc t ı̇)˙ → nthcT ṫ ı̄` es
> `pcc_eval_nthc` y la exige. Las cuatro casillas `wit` reales la cumplen (`decide`).
>
> ✅✅ **LA LÍNEA ROJA DE ADR-020, COMPROBADA Y CON RAZÓN ESTRUCTURAL**: `d3_prf_of_chainOkDot` y
> `pcc_lineWF_tracked_modulo_7` **conservan su firma exacta**. La guarda va DENTRO del `⇔` OBJETO,
> así que al reflector le llega como conjunto objeto extraído de `lineWF t`, **no** como hipótesis
> Lean — y por tanto no puede aparecer en su firma. Era el argumento que sostenía la vía; ahora es
> una comprobación.
>
> Estado autoritativo: **[NEXT-STEPS.md](NEXT-STEPS.md)** → **[CURRENT-STATUS-PROJECT.md](CURRENT-STATUS-PROJECT.md)**
> (⚠️ `PLAN-FRENTE-A.md` ya **no** es autoritativo: su pregunta —«¿vuelve la capa rastreada?»— está **contestada** desde el 2026‑08‑23)
> → [cuarentena/README.md](cuarentena/README.md) → [sondeos/README.md](sondeos/README.md).
> Catálogo de módulos y proyección: **[REFERENCE.md](REFERENCE.md)** §1 →
> [doc/REFERENCE-Incompleteness.md](doc/REFERENCE-Incompleteness.md) §3.24–§3.51.
>
> **Build 145 jobs · 0 sorrys · Lean v4.31.0** ✅ **VERDE** (2026‑09‑10h).
>
> 🏁🏁🏁 **C3 CERRADO: `pcc_lineWF_tracked` es INCONDICIONAL** (§3.62). Los **21 tags** cableados.
> La cadena, en cinco pasos: `prf_hasWitF_liftfc` (§3.61, `Meta/LiftfcWitnessPrf.lean`, net‑0 puro)
> ⇒ `ind` (18) y `listInd` (20) con el nodo **`tcm`** de `STree` ⇒ **los SIETE** reflectores de
> sustitución ⇒ ⭐ `pcc_tag_vacuous`, que **paga** el `hOther` que §11/§11bis habían declarado
> «vacuo pero más honesto como hipótesis» ⇒ **`hbody`(a) de D3, incondicional**
> (`Meta/D3BodyPrf.lean`).
> ⭐⭐ **Y `premsOf` SÍ se evalúa** (§3.63, `Meta/ListEtaPrf.lean` + `Meta/PremsOfTagPrf.lean`): la
> obstrucción de §3.59.2 («21 axiomas con *pattern‑matching*, nada que evaluar sobre un argumento
> abstracto») le faltaba una frase — *mientras no se sepa la **LONGITUD***, que sale del propio
> bicondicional del tag. Las **21 ramas**, a nivel objeto, en 417 líneas.
> 🏁🏁🏁🏁 **2026‑09‑10g · D3 PROBADA — `axiom d3` RETIRADO** (§3.67).
> `d3_prf_real (φ) : Prf (provCodeC' φ ⇒ provCodeC' (provCodeC' φ))`. La **tercera condición de
> derivabilidad** de Hilbert‑Bernays‑Löb es un **teorema**, `GodelTwo.d3` pasa de `axiom` a
> `theorem` ⇒ **la cadena D1/D2/D3 no postula ninguna de las tres**, y `goedel_second'` ya no
> depende de `d3`. **5 `axiom` de Lean** (eran 7).
> ⭐ **La QUINTA variante de `substfc_inv_*`** —nivel actuante **igual** al hueco bajo— es la **más
> barata de la familia**: el testigo **no aparece** en el resultado, luego no hace falta la
> hipótesis `u ≐ varc v̄` que la cuarta sí pedía. ⚠️ Van **cinco veces** que el índice no es
> cosmético; el inventario completo está en §3.67.3.
> ⚠️ **Tres trampas de FORMA nuevas** (§3.67.2): una hipótesis que **no viajaba** por el genérico;
> `rfl` desplegando `strCode` **carácter a carácter** hasta agotar los heartbeats; y el Leibniz que
> **captura** la variable si no se protege el hueco con `liftTerm`.
>
> 🏁🏁 **2026‑09‑10f · B1 y B2 CERRADAS, y B3 en 8 de 9** (§3.64–§3.66).
> **B1** (`Meta/PremsOfDotPrf.lean`): `pcc_eval_premsOf` — `premsOf` reflejado **dentro de `Prov`**
> con `t` abstracto, las 21 ramas. **B2** (`Meta/D3BodyPrf.lean` §2–§3): la **cota** cruzada, con B1
> en el eslabón que faltaba; ⚠️ los dos eslabones intermedios son **condicionales** ⇒ hizo falta
> `PrfH_pcc_rw`. **B3** (`Meta/PremsBdAllPrf.lean`): el chasis interior con sus **ocho**
> administrativas, más `substfc_id_substCodeF2` (la **cuarta** variante de la familia) y la
> naturalidad de `substCodeF2` en sus dos testigos.
> ⭐⭐ **Y ADR‑021 se AFINA** (§3.66.1): lo que rompe la naturalidad del `PsiF` **no es «ser un
> `substCodeF`»**, es que **el PARÁMETRO VIAJE DENTRO DE LA FÓRMULA**. Enunciada así predice los
> dos casos —el exterior, donde `hPl` era falsa, y el interior, donde es cierta—.
> ⬜ **D3 queda en UNA obligación con nombre**: `DEUDA_premsBody`, la novena del chasis interior,
> con la ruta medida (la única fricción es la **MONEDA de §3.55.2 por cuarta vez**, y sus dos
> piezas ya existen).
>
> 🔑🔑 **Las dos lecciones de método del día, y son recíprocas la una de la otra:**
> 1. ⚠️ **Una obligación declarada VACUA sin pagarla sigue contando como ABIERTA** aguas abajo
>    (§3.62.3). Ésta se arrastró como parámetro dos módulos y tres sesiones; pagarla costó veinte
>    líneas.
> 2. ⚠️ **Medir un frente por el TAMAÑO del molde sobreestima** (§3.61.3): el molde incluye lo que ya
>    está comprado. La medida útil se lee de su bloque `export`, no de su `wc -l`.
>
> 🏁🏁 **`pcc_eval_liftfc` PROBADO** (§3.53): sin hipótesis, con `v` y `X` abstractos y sólo
> `hasWitF X` de guarda, net‑0.
> 🏁 **D3: destino fijado, puente de la cota, `∃` acotado, cuerpo del `∀`, empaquetado, `PsiF`
> exterior, `hmatch`, `hPinv`, `hPsiId` y `hwP`: probados** (§3.55–§3.58).
> 🧹 **Dedup ADR‑019 de SEIS familias** (§3.52).
> ⛔ **Trampa del día, tres veces**: `substfc`/`carc`/`lenc`… son símbolos OBJETO y **no reducen**.
> **131 módulos activos** (Minimal 11 + Meta 109 + Full 11) **+ 0 en `cuarentena/` + 61 en `sondeos/`.**
> **5 `axiom` de Lean · 141 axiomas objeto** en `axioms` — ⚠️ la enmienda **sustituye 7 de los 141**,
> no añade ninguno: las listas no cambian de longitud y el inventario de Lean sigue en 7.
>
> 🏁 **`∀t. hasWit (tcFn t)` PROBADO** y en producción (`Meta/HasWitTcFnPrf.lean`), footprint
> `[propext, Classical.choice, Quot.sound]` — **net-0 puro**.
>
> ### Reparada la inconsistencia conocida (ADR-012/013)
>
> * `ax_tc_cons` **RETIRADO** de `axioms` (hacía la teoría **inconsistente**). El `def` sigue en
>   `Minimal/Axioms.lean:827` pero **fuera de las listas** — es una definición muerta.
> * **`goedel_first_real'`, `godelC'_fixedpoint` y `goedel_first_undecidable_real'` YA NO EXISTEN.**
>   Gödel I es hoy **`goedel_first_numeral`** (`Meta/DiagonalNumeral.lean`), sobre la sentencia 🗑️ *(lo que esta línea cita de `⊢` quedó retirado con esa capa, ADR-115)*
>   **numeral** `godelCN`.
> * **`cuarentena/` VACÍA** (0 módulos): D3 y Gödel II están **repatriados a la cadena activa**.
>   ⚠️ Que estén dentro del build no los hace probados — ver la fila de D3 y `NEXT-STEPS.md`.
> * ⚠️ **NO es una prueba de consistencia**: se retiró la inconsistencia **conocida y localizada**.
>
> ### La ESCALERA (a.2) COMPLETA — 4 de 4
>
> `pcc_eval_add` → `pcc_eval_mul` → `div2` → **`pcc_dot_cons`** (`Meta/DotConsPrf.lean`): la
> Σ₁‑completitud **internalizada** para argumentos ABSTRACTOS. Rédito verificado en
> `archivo/sondeos-2026-10:sondeos/CarcPayoff.lean`. ▶ **PASO 1 EJECUTADO (2026-08-23)**: `EvalListPrf` repatriado, y con él
> **6 módulos más en cascada** — cuarentena **21 → 12**. ▶ **PASO 2 EJECUTADO**: `EvalNthcPrf` + `EvalCarcNthcPrf` de vuelta (cuarentena 14 → 12). ▶ **PASO 3 EJECUTADO**: `D3InDotPrf` de vuelta ⇒ **D3 reducida otra vez a UN SOLO lema**. ▶ **PASOS 4‑5 EJECUTADOS**: `LineWFTrackedPrf` y el **KIT** (`CodeCtorKit`) en producción. **LA CUARENTENA ESTÁ VACÍA.**
>
> ⚠️ **`⊬¬G` sigue SIN cerrar** en la cadena real (falta `NegVerifier`); es frente independiente.

## `DECISIONS.md` — sus líneas 5–76, retiradas el 2026-10-16

> ## 🏁🏁 ESTADO REAL — 2026‑10‑05 · `master` · **`ConsistentH` es un TEOREMA del build: Gödel I y II sin hipótesis DENTRO de Lean** ([ADR‑120](#adr-120)) · la consistencia es **RELATIVA a Lean** ([ADR‑138](#adr-138))
>
> `consistencia : ConsistentH`, `goedel_I : ¬ Prf godelCN` y `goedel_II : ¬ Prf consistencyFormula'`
> (`Meta/Consistencia.lean`), por un modelo de los 142 (`MNV V₀`) y la solidez de `Prf` (`prf_sound`). 🏁 Y desde
> ADR‑121, Gödel I ENTERO (`goedel_I_neg`), E10 (`G` y `Con` verdaderas en el modelo) y Tarski. ⚠️ No dice: Rosser (⬜).
>
> ✏️ *(2026‑10‑16, [ADR‑138](#adr-138))* **Consistencia RELATIVA, no absoluta.** `consistencia` es una prueba EN LEAN;
> lo que garantiza fuera de Lean es PRA ⊢ Con(Lean) → Con(T_Prf), si el núcleo implementa bien esa teoría. No
> puede ser absoluta: `T_Prf` contiene a PA y, por Gödel II, ninguna teoría contenida en ella demuestra su
> consistencia. «Sin hipótesis» quiere decir sin hipótesis dentro de Lean. [TEOREMAS-E-HIPOTESIS.md](TEOREMAS-E-HIPOTESIS.md) §4.
>
> 🗓️ *Lo que sigue es el estado del 2026‑10‑04, como registro.*

> ## ESTADO REAL — 2026‑10‑04 · `master` · 🏁 **F1 reparado: Gödel I/II sobre `Prf` dependen sólo de `ConsistentH`** ([ADR‑117](DECISIONS.md))
>
> `axiomsCodeT` queda anclado por un axioma objeto DIAGONAL (L2‑3): `axioms` = **142** = los 141 de siempre
> (`axiomsBase`) y `ax_axiomsCodeT_def`, el último. El ancla de antes, la hipótesis de clase `AnclaEq`, es hoy
> el teorema `prf_ancla` (la clase se retiró con ADR‑118), y `goedel_first_prf` y `goedel_second_prf` ya no la llevan:
> su footprint sigue siendo los tres de Lean, y **F1 ya no los hace vacuos**. ⚠️ Siguen siendo **CONDICIONALES**:
> `ConsistentH` sólo vale si los 142 axiomas son consistentes, y no hay modelo; y `⊬¬G` sigue sin existir en
> ningún cálculo (irá por Rosser, sobre `Prf`).
>
> ### 2026‑10‑02 · 🗑️ **la capa `⊢` RETIRADA** ([ADR‑115](DECISIONS.md)) · ⛔ **Gödel I/II sobre `Prf`: VACUOS** por `[AnclaEq]` hasta ADR‑117 (F1, [ADR‑114](DECISIONS.md))
>
> RPP ya no usa `⊢` (`Derives`): **cinco de sus siete postulados son falsos** —las cuatro meta‑reglas de FOL
> (`imp_intro`, `raa`, `or_elim`, `ex_elim`) y el `axiom` `ax_list_induction` de RPP (retirado) se **refutan sin
> usarlos** (`sondeos/MetaReglasRefutables.lean`, compilado)—; los otros dos, también retirados (`ax_induction_prim`,
> `ax_axiomsCodeT_eq`, retirado con ellos), no se midieron. Se borraron **27 módulos**
> (`Minimal/Theorems/Block1–8`, ocho de `Full/`, nueve de `Meta/`) y **633 declaraciones**; la cadena
> de Gödel sobre `Prf` no usaba ninguna (medido por cierre de dependencias) y compila igual. RPP queda
> con **0 `axiom` de Lean**.
> ⛔ **Lo que NO arregla** *(hasta ADR‑117, 2026‑10‑04)*: `goedel_first_prf` y `goedel_second_prf` llevan la clase
> `[AnclaEq]`, y `AnclaEq` **da `Prf ⊥`** (F1, [ADR‑114](DECISIONS.md), `sondeos/AnclaEqInconsistente.lean`) ⇒ hoy
> los dos teoremas son **VACUOS**. Repararlo (L2‑3: anclar `axiomsCodeT` por punto fijo) es lo siguiente.
>
> ### 🗄️ Registro — el «ESTADO REAL» del 2026‑09‑11
>
> Titulaba «CADENA DE GÖDEL FINITARIA (Gödel I y II sobre `Prf`, hipótesis mínima `ConsistentH`, un solo
> axioma en el footprint) · `axioms ⊢` es COMPLETO». Lo de la hipótesis mínima y el solo axioma dejó de ser
> cierto con ADR‑026 (el ancla pasó a la firma como `[AnclaEq]`; lo primero vuelve a serlo desde ADR‑117), y `⊢`
> ya no está en RPP. Se conserva:
>
> Estado autoritativo: **[NEXT-STEPS.md](NEXT-STEPS.md)** → **[CURRENT-STATUS-PROJECT.md](CURRENT-STATUS-PROJECT.md)**
> (⚠️ `PLAN-FRENTE-A.md` ya **no** es autoritativo: su pregunta —«¿vuelve la capa rastreada?»— está **contestada** desde el 2026‑08‑23)
> → [cuarentena/README.md](cuarentena/README.md) → [sondeos/README.md](sondeos/README.md).
> Catálogo de módulos y proyección: **[REFERENCE.md](REFERENCE.md)** §1 →
> [doc/REFERENCE-Incompleteness.md](doc/REFERENCE-Incompleteness.md) §3.24–§3.32.
>
> **Build 129 jobs · 0 errores · 0 sorrys · Lean v4.31.0.**
> *(Cifras medidas el 2026-10-02, tras retirar la capa `⊢`: ADR-115; jobs, módulos, `axiom` y `sorry`, re‑medidos el 2026-10-04 con ADR-117, sin cambio; 129 jobs y 112 módulos desde el 2026-10-05, con `Minimal/SymLit.lean` (D7, ADR-129). En línea aparte para que `[A]` las compruebe: una línea con fecha ISO cuenta como registro y `[A]` la exime.)*
> **112 módulos activos** (Minimal 2 + Meta 107 + Full 3) **+ 0 en `cuarentena/` + 92 en `sondeos/`.**
> **0 `axiom` de Lean · 142 axiomas objeto** en `axioms` (los 141 de `axiomsBase` más el ancla, ADR‑117; `axioms_len`).
>
> ### Reparada la inconsistencia conocida (ADR-012/013)
>
> * `ax_tc_cons` **RETIRADO** de `axioms` (hacía la teoría **inconsistente**). El `def` sigue en
>   `Minimal/Axioms.lean:827` pero **fuera de las listas** — es una definición muerta.
> * **`goedel_first_real'`, `godelC'_fixedpoint` y `goedel_first_undecidable_real'` YA NO EXISTEN.**
>   Gödel I es hoy **`goedel_first_numeral`** (`Meta/DiagonalNumeral.lean`), sobre la sentencia 🗑️ *(lo que esta línea cita de `⊢` quedó retirado con esa capa, ADR-115)*
>   **numeral** `godelCN`.
> * **`cuarentena/` VACÍA** (0 módulos): D3 y Gödel II están **repatriados a la cadena activa**.
>   ⚠️ Que estén dentro del build no los hace probados — ver la fila de D3 y `NEXT-STEPS.md`.
> * ⚠️ **NO es una prueba de consistencia**: se retiró la inconsistencia **conocida y localizada**.
>
> ### La ESCALERA (a.2) COMPLETA — 4 de 4
>
> `pcc_eval_add` → `pcc_eval_mul` → `div2` → **`pcc_dot_cons`** (`Meta/DotConsPrf.lean`): la
> Σ₁‑completitud **internalizada** para argumentos ABSTRACTOS. Rédito verificado en
> `archivo/sondeos-2026-10:sondeos/CarcPayoff.lean`. ▶ **PASO 1 EJECUTADO (2026-08-23)**: `EvalListPrf` repatriado, y con él
> **6 módulos más en cascada** — cuarentena **21 → 12**. ▶ **PASO 2 EJECUTADO**: `EvalNthcPrf` + `EvalCarcNthcPrf` de vuelta (cuarentena 14 → 12). ▶ **PASO 3 EJECUTADO**: `D3InDotPrf` de vuelta ⇒ **D3 reducida otra vez a UN SOLO lema**. ▶ **PASOS 4‑5 EJECUTADOS**: `LineWFTrackedPrf` y el **KIT** (`CodeCtorKit`) en producción. **LA CUARENTENA ESTÁ VACÍA.**
>
> ⚠️ **`⊬¬G` sigue SIN cerrar** en la cadena real (falta `NegVerifier`); es frente independiente.


## `DECISIONS.md` — su línea 8, la marca vieja que seguía debajo del banner, retirada el 2026-10-16

**Última actualización:** 2026-09-10h — **ADR-022**: la clase de testigos de la ω‑consistencia se ESTRECHA a líneas estándar; el precio (una `OmegaConsistent` más fuerte) va escrito, y la garantía que lo hace admisible (`stdChain_proofCode'`) probada. — (previo 2026-09-05) **ADR-019 confirmado en vivo por B3**: el general mal colocado dejaba un corolario inalcanzable, y la duplicación por INSTANCIA que ningún censo ve. ADR-018 en producción.

## `doc/REFERENCE-Incompleteness.md` — sus banners de cabecera, retirados el 2026-10-21

*(Los enlaces relativos de dentro son los de su documento de origen, en `doc/`.)*

> 🏁 **2026‑10‑04 · ADR‑117 — F1 reparado.** `axioms` tiene 142 fórmulas: los 141 de `axiomsBase` y, la última, el
> axioma DIAGONAL `ax_axiomsCodeT_def`. El ancla `axiomsCodeT =eq listFormCodeM axioms` es un TEOREMA (`prf_ancla`,
> `Meta/Representability2Prf.lean`) y la clase `AnclaEq` se retiró (ADR‑118). `goedel_first_prf` y
> `goedel_second_prf` toman sólo `(hcon : ConsistentH)`, con los tres axiomas de Lean: F1 ya no los hace vacuos.
> ⚠️ Siguen CONDICIONALES: `ConsistentH` vale sólo si los 142 son consistentes (✏️ desde ADR‑120 lo son: `consistencia`, y `goedel_I`/`goedel_II` van sin hipótesis);
> `f1_traduccion_refutada` bloquea el argumento de F1 (si la traducción conservara el ancla, ya habría `Prf ⊥`; no
> prueba la consistencia). `⊬¬G` sigue sin existir:
> irá por Rosser, sobre `Prf`. *(✏️ 2026‑10‑14, [ADR‑134](../DECISIONS.md): registro del 2026‑10‑04. Desde ADR‑121 la
> mitad `⊬¬G` es `goedel_I_neg`, por la solidez en el modelo, sin Rosser; y desde ADR‑120 `ConsistentH` es teorema.)*

> 🗑️ **2026‑10‑02 · ADR‑115.** La capa `⊢` se retiró: de `Meta/` salen 9 módulos (`AxiomListCode`,
> `DerivCond`, `Induction`, `LineWFDerives`, `ListInductionArith`, `Necessitation`, `OmegaStrength`,
> `Reflection`, `StepArith`) y todo lo enunciado sobre `⊢` en los demás, retirado también — `goedel_first_numeral`,
> `goedel_second'`, `NegVerifier` y la mitad `⊬¬G`. La cadena sobre `Prf` (D1 `repr_pos'_prf`, D2
> `d2_prf`, D3 `d3_prf_real`, `goedel_first_prf`, `goedel_second_prf`) **sigue entera**, y ⛔ **sigue
> vacua** por `[AnclaEq]` (F1, ADR‑114; hasta ADR‑117, 2026‑10‑04: ver arriba). Las secciones de abajo que
> hablan de `⊢` son registro.

**Contenido:** la aritmetización real de las condiciones de Hilbert-Bernays sobre el cálculo finitario
`Prf` — Gödel I (`goedel_first_numeral`), D1 (`repr_pos'_prf`), D2 (`d2_prf`), Gödel II núcleo 🗑️ *(lo que esta línea cita de `⊢` quedó retirado con esa capa, ADR-115)*
(`goedel_second'`) — 🏁 **D3 DEMOSTRADA** el 2026‑09‑10g (`d3_prf_real`), con lo que la cadena
D1/D2/D3 **no postula ninguna de las tres**.

> ## ⚠️ ESTADO REAL — 2026-08-23 · repatriación paso 1 hecha
>
> **Build 134 jobs · 118 módulos activos** (Minimal 2 + Meta 114 + Full 2) **+ 0 en `cuarentena/`
> + 44 `sondeos/` · 0 `axiom` de Lean · 142 axiomas objeto · 0 errores / 0 sorrys.**
> *(Cifras medidas el 2026-10-02, tras retirar la capa `⊢`: ADR-115. En línea aparte para que `[A]` las compruebe: una línea con fecha ISO contaba como registro y `[A]` la eximía. ✏️ Desde ADR‑169 la fecha ya no exime: las líneas de abajo llevan «Entonces:».)*
> *(Re‑medidas el 2026-10-04 tras ADR-117: de estas cifras sólo cambian los axiomas objeto, de 141 a 142 —la base y el ancla diagonal—.)*
> *(Entonces: el 2026-10-05, con D7 (ADR-129): 129 jobs y 112 módulos, por `Minimal/SymLit.lean`; los `sondeos/` son hoy 88.)*
> *(Entonces: el 2026-10-17, con ADR-148: 131 jobs y 114 módulos, por `Meta/RosserW1.lean`, la etapa W1(ax) de Rosser.)*
> *(Entonces: el 2026-10-17, con ADR-149: 132 jobs y 115 módulos, por `Meta/RosserPosNum.lean`, la etapa 6 de Rosser.)*
> *(Entonces: el 2026-10-17, con ADR-150: 133 jobs y 116 módulos, por `Meta/RosserNumerales.lean`, la etapa 1 de Rosser.)*
> *(Entonces: el 2026-10-17, con ADR-152: 134 jobs y 117 módulos, por `Meta/RosserNumEval.lean`, la etapa 2 de Rosser.)*
> *(Entonces: el 2026-10-17, con ADR-153: 135 jobs y 118 módulos, por `Meta/RosserGuardNeg.lean`, la etapa 3 de Rosser.)*
> *(Entonces: el 2026-10-17, con ADR-154: 136 jobs y 119 módulos, por `Meta/RosserNegLinea.lean`, la etapa 4 de Rosser.)*
> *(Entonces: el 2026-10-17, con ADR-156: 137 jobs y 120 módulos, por `Meta/RosserNegNum.lean`, la etapa 5 de Rosser.)*
> *(Entonces: el 2026-10-18, con ADR-157: 139 jobs y 122 módulos, por `Meta/Rosser.lean`, Rosser, y `Meta/PurezaComando.lean`, la herramienta de T08.)*
> *(Entonces: el 2026-10-18, con ADR-159: 140 jobs y 123 módulos, por `Meta/Lob.lean`, Löb.)*
> *(Entonces: el 2026-10-18, con ADR-160: 135 jobs y 118 módulos: T66 retiró del build `ChainNegPrf`, `VerifierSound`, `OmegaReflect`, `ChainDecode` y `CodeDecode`, sin consumidor; los sondeos, 43.)*
> *(Entonces: el 2026-10-18, con ADR-161: 130 jobs y 113 módulos: el paso 3 de ADR-139 retiró `CodeDistinct`, `ReflectionPrf`, `Sigma1TrackedPrf`, `Sigma1BoundedPrf` y `Full/PrimeFactor`, sin nada en el cono.)*
> *(Entonces: el 2026-10-18, con ADR-162: 131 jobs y 114 módulos, por `Meta/GodelCorolarios.lean`, los corolarios de T78.)*
> *(Entonces: el 2026-10-18, con ADR-165: 133 jobs y 116 módulos, por `Meta/ContratoTitulares.lean` y `Meta/ContratoTabla.lean`, T07.)*
> *(Entonces: el 2026-10-19, con ADR-170: 132 jobs y 116 módulos, porque `FOL.Deduction`, sin nada en el cono, salió del build, T74.)*
> *(Entonces: el 2026-10-20, con ADR-173: 133 jobs y 117 módulos, por `Meta/RigidezEstandar.lean`, T75e.)*
> *(Entonces: el 2026-10-20, con ADR-175: 134 jobs y 118 módulos, por `Meta/SegundoModelo.lean`, T75d.)*
>
> ### Dos cambios estructurales que este nodo documenta a partir de §3.24
>
> 1. **La REPARACIÓN (2026‑08‑18/19, [ADR‑012](../DECISIONS.md)).** `ax_tc_cons` **retirado** de
>    `axioms`: hacía la teoría objeto **inconsistente**. Los códigos de Gödel pasan a escribirse como
>    **NUMERALES** (`numeral (codeNat φ)`), no como árboles `cons`. En consecuencia:
>    * **`goedel_first_real'`, `godelC'_fixedpoint` y `goedel_first_undecidable_real'` YA NO
>      EXISTEN.** Gödel I es hoy **`goedel_first_numeral`** (§3.24.2), sobre la sentencia `godelCN`. 🗑️ *(lo que esta línea cita de `⊢` quedó retirado con esa capa, ADR-115)*
>    * 21 módulos a **cuarentena** ([ADR‑013](../DECISIONS.md)) — sus teoremas eran formalmente
>      correctos pero **vacuos**, probados sobre una teoría que probaba ⊥.
>    * ⚠️ **NO es una prueba de consistencia**: se retiró la inconsistencia **conocida y localizada**.
> 2. **La ESCALERA (a.2, 2026‑08‑19/22).** La Σ₁‑completitud **internalizada** que devuelve la
>    cuarentena: `pcc_eval_add` → `pcc_eval_mul` → `div2` → **`pcc_dot_cons`** (§3.25). **Completa.**
>
> **Secciones §3.15–§3.23 son ANTERIORES a la reparación.** Lo que describen sobre la capa rastreada
> (los 21 tags, `hI_dot`, el chasis, el KIT) sigue siendo una descripción fiel del **código en
> `cuarentena/`**, pero **ese código no está en el build** y sus enunciados cambiarán al repatriarse
> (los códigos estáticos pasan de `termCode (formCode φ)` a `termCode (numeral (codeNat φ))`).

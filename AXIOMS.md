# Registro central de axiomas — ROBINSON_PlusPlus

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
> **112 módulos activos** (Minimal 2 + Meta 107 + Full 3) **+ 0 en `cuarentena/` + 89 en `sondeos/`.**
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
> `sondeos/CarcPayoff.lean`. ▶ **PASO 1 EJECUTADO (2026-08-23)**: `EvalListPrf` repatriado, y con él
> **6 módulos más en cascada** — cuarentena **21 → 12**. ▶ **PASO 2 EJECUTADO**: `EvalNthcPrf` + `EvalCarcNthcPrf` de vuelta (cuarentena 14 → 12). ▶ **PASO 3 EJECUTADO**: `D3InDotPrf` de vuelta ⇒ **D3 reducida otra vez a UN SOLO lema**. ▶ **PASOS 4‑5 EJECUTADOS**: `LineWFTrackedPrf` y el **KIT** (`CodeCtorKit`) en producción. **LA CUARENTENA ESTÁ VACÍA.**
>
> ⚠️ **`⊬¬G` sigue SIN cerrar** en la cadena real (falta `NegVerifier`); es frente independiente.

**Last updated:** 2026-07-22 — **nueva §1.1: por qué la inducción de `Full/` es el mínimo teórico de Gödel II** (Q no satisface D2/D3; reparto verificado con `#print axioms`: D1 y D2 limpios, Gödel I/II usan `Full.ax_induction`+`ax_list_induction`). Sin cambios en el inventario: siguen **7**. — (previo 2026-07-20) **`prf_inAxC` → `prf_axiomsCodeT_eq`** (espejo `Prf` del ancla de igualdad; `prf_inAxC` pasa a **teorema**, **net‑0 axiomas**; lo exige el `In`‑reflect de `axiomsCodeT`). Total **7** `axiom`, sin cambio de número. (previo 2026-07-13: `ax_inAxC` → `ax_axiomsCodeT_eq`, net‑0, desbloquea `⊬¬G`. Previo 2026-07-09: F7a, 14 → 7.)
**Author:** Julián Calderón Almendros

Registro autoritativo de **todas** las declaraciones `axiom` de Lean que sostienen
el proyecto: qué son, por qué son legítimas (o pendientes), y en qué módulo viven.

> **Por qué NO están todas en un solo módulo.** El instinto de «todos los axiomas
> en un sitio» choca con la estratificación deliberada del proyecto. Los axiomas
> pertenecen a **capas conceptualmente distintas** y su domicilio es una decisión
> de diseño, no descuido:
>
> - **Minimal vs Full es una frontera.** `Minimal/` está *definido* como el sistema
>   débil SIN inducción general (≈ Robinson Q). El esquema de inducción vive en
>   `Full/` porque es justo lo que Full **añade**; moverlo a Minimal arrastraría
>   toda la maquinaria de Full y borraría la frontera.
> - **Teoría objeto vs metateoría.** Los esquemas aritméticos son de la teoría
>   objeto; `d3` es metamatemático (sobre demostrabilidad). Son niveles distintos.
> - **Dos cálculos.** `Derives` (`⊢`) y `Prf` necesitan cada uno su ancla de
>   codificación (`ax_axiomsCodeT_eq` / `prf_axiomsCodeT_eq`); no son un duplicado a fusionar. 🗑️ *(lo que esta línea cita de `⊢` quedó retirado con esa capa, ADR-115)*
>   ✏️ **2026‑10‑04 ([ADR‑117](DECISIONS.md))**: hoy sólo queda `Prf`, y su ancla no es un `axiom` de Lean sino el
>   axioma OBJETO `ax_axiomsCodeT_def`, el 142.º de `axioms` (ver «Anclas de codificación», más abajo).
>
> Este fichero es el «sitio único» **documental**: la fuente de verdad sobre el
> inventario, aunque el código mantenga cada axioma en su capa correcta.

---

## 1 · Axiomas de Lean en ROBINSON_PlusPlus — **0** desde el 2026‑10‑02

> 🗑️🗑️ **2026‑10‑02 · CERO ([ADR‑115](DECISIONS.md)).** Los tres que quedaban, hoy retirados —`ax_induction_prim`,
> `ax_list_induction` y `ax_axiomsCodeT_eq`— eran postulados **sobre `⊢`**, y quedaron retirados con esa capa.
> `ax_list_induction` (retirado) era además **falso**: daba `[] ⊢ ⊥` con dos constructores (L1‑2,
> `sondeos/ListInductionAxiomRefutable.lean`); y las cuatro meta‑reglas de FOL que `⊢` traía también lo
> son (L1‑3, `sondeos/MetaReglasRefutables.lean`). La tabla de abajo es el **REGISTRO** de lo que hubo.
> ⛔ Lo único postulado que quedaba en el proyecto era la **clase `AnclaEq`** (hipótesis de instancia, no
> `axiom`), y **daba `Prf ⊥`** (F1, ADR‑114). 🏁 Desde el 2026‑10‑04 ([ADR‑117](DECISIONS.md)) el ancla es un
> TEOREMA (`prf_ancla`), que sale del axioma OBJETO diagonal `ax_axiomsCodeT_def`, el 142.º de `axioms` (ver
> «Anclas de codificación», más abajo); y la clase se RETIRÓ el 2026‑10‑05 ([ADR‑118](DECISIONS.md)).


> ⚠️ Esta cabecera decía **(7)** con la fila 7 tachada justo debajo. Lo cazó
> `doc/book/AUDITORIA-2026-09-10.md` R3.

> ⚠️⚠️ **LA COLUMNA `#` SE RETIRA (2026‑09‑12).** Era un **acoplamiento por número de fila**:
> `doc/book/capitulos/cap-representabilidad-d1.tex:70` cita *«los axiomas **5 y 6**»* de esta tabla,
> y **ningún control detecta** que al retirar un axioma esa referencia pase a apuntar a otro sitio.
> Ha pasado **dos veces en un día** (Ax‑P retirado y el ancla `Prf` convertida en hipótesis).
> 🔑 **Se cita por NOMBRE, nunca por número.**

| Axioma | Módulo | Familia | Naturaleza |
|--------|--------|---------|------------|
| ~~`ax_induction_prim`~~ | ~~`Full/Induction.lean`~~ | 🗑️ **RETIRADO el 2026‑10‑02** ([ADR‑115](DECISIONS.md)) · era: esquema de inducción | Axioma legítimo de la teoría objeto (IΣ₁/PA), **sobre los 23 primitivos**: `primAxioms ⊢ inductionFormula φ`. 🆕 **RATIFICADO el 2026‑09‑10h** ([ADR‑023](DECISIONS.md)) — dice lo que `Full` significa: *los primitivos **más** el esquema*. ⚠️ `ax_induction` (sobre `axioms`) **ya NO es un `axiom`**: es teorema por debilitamiento ⇒ el recuento **no sube** 🗑️ *(lo que esta línea cita de `⊢` quedó retirado con esa capa, ADR-115)* |
| ~~`ax_list_induction`~~ | ~~`Full/Lists.lean`~~ | 🗑️ **RETIRADO el 2026‑10‑02** ([ADR‑115](DECISIONS.md)) · era: esquema de inducción, y **FALSO** (L1‑2) | Inducción estructural sobre listas del objeto. ⚠️ Con la codificación anterior (`cons a b = pair a (σb)`) era **falso en ℕ**: los triangulares no son `nil` ni `cons` ([ADR‑088](DECISIONS.md), `sondeos/ModeloBasura.lean`). Desde [ADR‑113](DECISIONS.md) (`cons a b = σ (pair a b)`, 2026‑09‑28) todo número es `nil` o `cons`, y lo verdadero en ℕ es la regla `listInd` de `Prf` (`sondeos/CantorSobreyectivo.lean`); ✏️ el axioma no lo era en ninguna codificación: su `φ` era una función de Lean y daba `[] ⊢ ⊥` (L1‑2) 🗑️ *(lo que esta línea cita de `⊢` quedó retirado con esa capa, ADR-115)* |
| ~~`ax_mod2_alternation`~~ | ~~`Full/Mod2.lean`~~ | 🏁 **RETIRADO el 2026‑09‑10h** | Era `∀n, mod2(σn) + mod2(n) = 1`. Hoy es **teorema**, derivado de `ax21` (rango) + `ax16` + `ax4` + `zero_add` + `teo_1_11`. ⚠️ Su propio docstring ya decía que en `Minimal` era derivable; lo que ocultaba era una **circularidad**: `ax21` se «derivaba» de él, y él de `ax21`. Medido cuál es el primitivo: **`ax21`** (`ax16 + ax17` admiten `mod2 2̄ = 2̄`) |
| ~~`ax_p_tfa`~~ | ~~`Minimal/Theorems/Block8.lean`~~ | 🗑️ **RETIRADO el 2026‑09‑12** | Era el TFA en forma idealizada. **Medido HUÉRFANO**: cero consumidores, y `IsFactorization` —el tipo que habitaba— **no aparecía ni una vez** fuera de `Block8.lean`. ⚠️⚠️ **Y con él cae una afirmación MEDIBLE‑MENTE FALSA que esta tabla publicó durante meses**: «*teorema en Full, postulado en Minimal*». **No existe en `Full/` ningún teorema con este enunciado.** `tfa_numeral` tiene **otro dominio** (`Nat` vs `Term`), **otra unicidad** (`Perm` vs igualdad objeto) y **otra hipótesis** (meta vs objeto) — su propio docstring lo dice: «no discharge constructivo por el Muro 1» |
| ~~`ax_axiomsCodeT_eq`~~ | `Minimal/Axioms.lean` | 🗑️ **RETIRADO el 2026‑10‑02** ([ADR‑115](DECISIONS.md)) · era: ancla de codificación sobre `⊢` | **`axioms ⊢ (axiomsCodeT =eq listFormCodeM axioms)`** — `axiomsCodeT` **es** el código de la lista de axiomas (extensión conservadora, cálculo `⊢`). **Reemplaza a `ax_inAxC`** (2026‑07‑13), que pasa a ser **teorema** derivado; a diferencia de `ax_inAxC` (sólo positivo), da **ambas direcciones** — la negativa `neg_In_axiomsCodeT` (que SÓLO los axiomas están) desbloquea `⊬¬G` (ver `PLAN-NEGVERIFIER.md`). El término gigante NO se materializa (recursión estructural, `Meta/AxiomListCode.lean`) 🗑️ *(lo que esta línea cita de `⊢` quedó retirado con esa capa, ADR-115)* |
| ~~`prf_axiomsCodeT_eq`~~ | ~~`Meta/Representability2Prf.lean`~~ | 🗑️ **YA NO ES `axiom`** (2026‑09‑12, [ADR‑026](DECISIONS.md)) | 🏁 **Desde ADR‑117 (2026‑10‑04), TEOREMA**: `prf_ancla : Prf (axiomsCodeT =eq listFormCodeM axioms)` (`Meta/Representability2Prf.lean`, footprint `[propext, Classical.choice, Quot.sound]`), que sale del axioma OBJETO diagonal `ax_axiomsCodeT_def`, el 142.º de `axioms`. La clase se retiró el 2026‑10‑05 (ADR‑118), y ninguna firma la lleva. ¿Quién la descarga? **`prf_ancla`**. Registro, hasta ADR‑117: era la **clase `AnclaEq`**, hipótesis de instancia. ⛔⛔ **El postulado NO desapareció: se movió del footprint a la FIRMA.** `goedel_first_prf`/`goedel_second_prf` dan hoy `[propext, Classical.choice, Quot.sound]` —cero axiomas del proyecto— **pero su tipo es `∀ [AnclaEq], …`** y **no hay ninguna `instance : AnclaEq` en el árbol** [medido]. Anunciar el footprint sin esta frase sería **M‑8**. ¿Quién la descarga? **Nadie** — `TEOREMAS-E-HIPOTESIS.md` §1 |
| ~~`d3`~~ | `Meta/GodelTwo.lean` | 🏁 **RETIRADO el 2026‑09‑10g** | Era la condición D3 de Hilbert‑Bernays‑Löb para `provCodeC'`. Hoy es **teorema**: `d3_prf_real` (`Meta/PremsBdAllPrf.lean` §10). ⇒ **la cadena D1/D2/D3 no postula ninguna de las tres** |

### 🆕 Nota 2026‑09‑10h — `ax_induction` y [ADR‑023](DECISIONS.md) 🗑️ *(lo que esta línea cita de `⊢` quedó retirado con esa capa, ADR-115)*

🏁 **RATIFICADO Y EJECUTADO** el 2026‑09‑10h. El movimiento —**no** un axioma nuevo— quedó así:

```lean
axiom ax_induction_prim (φ : Formula) : primAxioms ⊢ inductionFormula φ

theorem ax_induction (φ : Formula) : axioms ⊢ inductionFormula φ :=
  prim_to_axioms (ax_induction_prim φ)
```

⇒ `ax_induction` **deja de ser `axiom`** y el recuento **sigue en 6**. 🗑️ *(lo que esta línea cita de `⊢` quedó retirado con esa capa, ADR-115)*

Sirve para **certificar** el censo de `coreAxioms`: los 11 derivables se demostraban con enunciados
`axioms ⊢ axN` que son **triviales por `ax`**. Con el axioma en su sitio, **9 de los 11** están hoy
certificados sobre `primAxioms` (7 en `Full/Induction.lean`, 2 en `Full/Lists.lean`).

⛔ **La salida fácil estaba cerrada**: generalizarlo a `∀ {Γ}, Γ ⊢ inductionFormula φ` sería
**FALSO** (con `Γ = []` haría la inducción **lógicamente válida**). Un axioma **tiene que nombrar su
contexto**; `ax_list_induction` puede ser genérico porque es una **regla**, no un axioma. 🗑️ *(lo que esta línea cita de `⊢` quedó retirado con esa capa, ADR-115)*

🏁 **Y la pregunta previa se contestó el mismo día: `ax_mod2_alternation` era DERIVABLE.** No hubo 🗑️ *(lo que esta línea cita de `⊢` quedó retirado con esa capa, ADR-115)*
que moverlo: **se retiró**, y el inventario bajó de **6 a 5**.

⚠️⚠️ **Pero eso destapó una circularidad y obligó a corregir el censo.** `ax21` se «derivaba» de
`ax_mod2_alternation`, y `ax_mod2_alternation` se deriva de `ax21`. Mientras uno de los dos fue 🗑️ *(lo que esta línea cita de `⊢` quedó retirado con esa capa, ADR-115)*
**axioma**, el círculo no se veía. Medido cuál es el primitivo: **`ax21`** — `ax16 + ax17` **no**
fijan el rango de `mod2` (un modelo con `mod2 2̄ = 2̄` los satisface). ⇒ el censo pasa de
**23 + 11** a **24 + 10**, y `ax21` entra en `primAxioms`.

🏁🏁 **CENSO CERRADO: 10 DE 10** (2026‑09‑12). `ax24` **certificado** sobre los primitivos:
`mod2_of_even_prim : primAxioms ⊢ ax24_mod2_of_even`, footprint
`[propext, Classical.choice, Quot.sound, FOL.MetaRules.{ex_elim, gen, imp_intro, or_elim},
ax_induction_prim]` — **sin `ax_list_induction`, sin anclas, sin nada de `axioms`**. 🗑️ *(lo que esta línea cita de `⊢` quedó retirado con esa capa, ADR-115)*

⭐ **Salió más barato de lo previsto, y por una pieza**: la versión `axioms` usaba `teo_2_9` de
`Block1` —que vive sobre `axioms` porque allí `Γ := axioms`— y portarlo habría arrastrado medio
bloque. Se **evita** con **`add_eq_zero_right_prim`** (≈20 líneas) sobre `zero_or_succ_ax_prim`,
que **ya existía**. ⚠️ Y `teo_1_3`, que tres documentos daban como dependencia, era **prosa
obsoleta**: no se usaba.

⭐ Y la cadena entera (`teo_1_11_prim`, `mod2_zero_prim`, `ax_mod2_alternation_prim`, 🗑️ *(lo que esta línea cita de `⊢` quedó retirado con esa capa, ADR-115)*
`a_plus_one_eq_one_prim`, `mod2_two_k_eq_zero_prim`) quedó **sobre los primitivos**, con las firmas
`axioms ⊢` como **envoltorios** por `prim_to_axioms` ⇒ **ninguna prueba duplicada**.

### Detalle por familia

> 🗄️ **Registro, anterior a ADR‑115.** Hoy no hay esquemas `axiom`: la inducción de la cadena de Gödel entra
> por los constructores `Prf.ind` y `Prf.listInd`, y el ancla de codificación es, desde ADR‑117 (2026‑10‑04), el
> axioma OBJETO diagonal `ax_axiomsCodeT_def` (hasta entonces, la clase `[AnclaEq]`, que daba `Prf ⊥`: F1). Las
> cifras de abajo («quedan 6 axiomas»…) son de su fecha.

- **Esquemas de inducción (1–3, en `Full/`).** Son *la* inducción que el sistema
  `Full` añade sobre el débil `Minimal`. No pueden vivir en `Minimal/` sin destruir
  la frontera de diseño (Minimal = sin inducción general). `ax_mod2_alternation` 🗑️ *(lo que esta línea cita de `⊢` quedó retirado con esa capa, ADR-115)*
  es un axioma-puente que permite derivar `ax21`/`ax24` como teoremas.
  **No son andamiaje opcional: son el mínimo teórico de Gödel II — ver §1.1.**

### 1.1 · Por qué la inducción es IMPRESCINDIBLE (y no un lujo del formalizador)

> ✏️ **2026‑10‑02 (ADR‑115).** El argumento sigue en pie —Gödel II pide inducción—, pero hoy la inducción entra
> por los constructores `Prf.ind` y `Prf.listInd`, no por un `axiom`: `ax_induction` y `ax_list_induction` (retirados)
> se fueron con la capa `⊢`. La tabla y la «consecuencia arquitectónica» de abajo hablan de ellos: son registro.

> Pregunta recurrente: *si `Minimal` ≈ Robinson Q y Q es esencialmente indecidible,
> ¿no debería alcanzarse Gödel II sin inducción?* **No.** Y conviene dejarlo escrito
> porque el diseño en dos capas invita a pensar lo contrario.

**Hecho clásico.** Q es Σ₁‑completa *externamente*, pero **no satisface las condiciones
de derivabilidad de Hilbert–Bernays–Löb**: en particular **no prueba su propia
Σ₁‑completitud** (D3). Gödel II requiere D1–D3, y para D2/D3 hace falta inducción —
IΣ₁ (o EA/IΔ₀+exp) es el mínimo habitual. Gödel **I** sí llega sobre Q (vía Rosser);
Gödel **II**, no. Por tanto *«Gödel II sobre Q sin inducción»* no es un objetivo
pendiente de este proyecto: es un **enunciado falso**.

**Dónde entra exactamente, verificado con `#print axioms`** (no por conjetura):

| resultado | ¿usa `Full.ax_induction` / `ax_list_induction`? 🗑️ *(lo que esta línea cita de `⊢` quedó retirado con esa capa, ADR-115)* |
|---|---|
| **D1** `repr_pos'_prf` | **NO** — limpio (sólo el ancla de codificación) |
| **D2** `d2_prf` | **NO** — limpio (`[propext, choice, Quot.sound]`) |
| `goedel_first_numeral` (Gödel I) | **SÍ** 🗑️ *(lo que esta línea cita de `⊢` quedó retirado con esa capa, ADR-115)* |
| `goedel_second'` | **SÍ** — 🏁 y **sin `d3`** desde el 2026‑09‑10g |

El reparto encaja con la teoría: **D1 es la Σ₁‑completitud *externa*** (aplicar el
verificador a una derivación concreta = cómputo finito, sin inducción); **D3 es la
Σ₁‑completitud *provable*** — razonar dentro de la teoría sobre *todas* las líneas y
sobre funciones recursivas de la sintaxis (`substfc`, `runFn`, …), y **eso exige
inducción**. Es exactamente el muro con el que se topó B.3c en los tags `q1`/`q2`/`q3`/
`leibniz`/`ind`/`qconf`/`listInd` (ver `NEXT-STEPS.md`).

**Consecuencia arquitectónica (importante, y no obvia).** `ax_induction` tiene la forma 🗑️ *(lo que esta línea cita de `⊢` quedó retirado con esa capa, ADR-115)*
`axioms ⊢ inductionFormula φ`: **extiende la relación de derivabilidad del objeto**. Es
decir, la teoría cuya demostrabilidad aritmetiza `provCodeC'` **no es Q pelada, es
Q++ + inducción** (perfil IΣ₁) siempre que la cadena cite esos axiomas. `Minimal/` sigue
siendo la *lista* de axiomas débil y la frontera de diseño se mantiene, pero el sujeto
del teorema de incompletitud, en la cadena real, es el sistema **con** inducción.
Esto es lo correcto y lo esperado — sólo faltaba decirlo explícitamente.

**Corolario práctico:** al construir la Σ₁‑completitud provable **está permitido y es
necesario** usar la inducción de `Full/`. Lo que *no* está permitido es añadir axiomas
*nuevos* para esquivarla; en particular, la inducción fuerte sobre **códigos** es
**derivable sin axiomas nuevos** (`ax_L0_cons_def` ancla `cons h t = succ (pair h t)` desde ADR‑113
con `pair = cantor_func`, luego los códigos son números y vale `ax_induction`). 🗑️ *(lo que esta línea cita de `⊢` quedó retirado con esa capa, ADR-115)*
- 🗑️ ~~**Teoría objeto.** `ax_p_tfa`~~ — **retirado el 2026‑09‑12**, medido huérfano. Ver su fila.
- **Anclas de codificación.** Extensión **conservadora** (✏️ nunca se probó, y el ancla de `Prf` daba `Prf ⊥`: F1, ADR‑114). `ax_axiomsCodeT_eq` 🗑️ *(lo que esta línea cita de `⊢` quedó retirado con esa capa, ADR-115)*
  (cálculo `⊢`) es una **igualdad**: `axiomsCodeT` ES el código de la lista de
  axiomas — da **ambas** direcciones (positiva `ax_inAxC`, ahora **teorema**; y 🗑️ *(lo que esta línea cita de `⊢` quedó retirado con esa capa, ADR-115)*
  negativa `neg_In_axiomsCodeT`, que SÓLO los axiomas están). El término gigante
  `listFormCodeM axioms` **no se materializa** en las pruebas (recursión estructural,
  `Meta/AxiomListCode.lean`), evitando el coste que retiró el `ax_axiomsCodeT` 🗑️ *(lo que esta línea cita de `⊢` quedó retirado con esa capa, ADR-115)*
  original en `7ae7b7b`. **`prf_axiomsCodeT_eq`** (cálculo `Prf`; **retirado** como `axiom` el 2026‑09‑12, [ADR‑026](DECISIONS.md), `24b3550`: fue una hipótesis —la clase `AnclaEq`, sin instancia— hasta ADR‑117, y hoy es el teorema `prf_ancla`) es su espejo exacto:
  desde 2026‑07‑20 (`25d255b`) sustituye al antiguo `prf_inAxC` —que era sólo
  positivo y ahora es **teorema** derivado—, también **net‑0 axiomas**. Lo exige el
  `In`‑reflect de `axiomsCodeT` (`Meta/InAxiomsCodePrf.lean`), que necesita las **dos**
  direcciones dentro de `Prf`.
  ⭐ **2026‑10‑04 · [ADR‑117](DECISIONS.md) — el ancla de hoy es un axioma OBJETO**, no un `axiom` de Lean: el último
  de los **142** de `axioms` (los 141 de `axiomsBase` = 34 de `coreAxioms` + 107 de `codingAxioms`, y él).
  `ax_axiomsCodeT_def := axD axiomsBase` (`Minimal/Axioms.lean`) es el axioma DIAGONAL
  `axiomsCodeT =eq ⌜axiomsBase⌝ ++ [δ]`, con δ = `deltaD` = `substfc 0 (tcFn N̄) N̄` y N̄ = `nD`, el numeral (plegado)
  del código de la plantilla `psiD`. No se contiene a sí mismo —habla de la base—, y δ es, PROBADAMENTE, el código
  del propio axioma (`prf_deltaD`, el lema diagonal); de ahí sale el ancla de antes como TEOREMA, `prf_ancla`
  (`Meta/Representability2Prf.lean`), y `axioms_split : axioms = axiomsBase ++ [ax_axiomsCodeT_def]` (por `rfl`)
  sustituye a `axioms_eq`, retirado. ⛔ Nada puede EJECUTAR `axioms`: construiría el numeral entero (`check-sorry`
  vigila las órdenes que lo harían; las reducciones del núcleo recorren la espina y no despliegan el numeral).
  ⚠️ Lo que NO dice: que los 142 sean consistentes (✏️ hasta ADR‑120, que da un modelo: `consistencia`); `f1_traduccion_refutada` sólo prueba que,
  si la traducción de F1 conservara el ancla —si su imagen fuera teorema—, ya habría `Prf ⊥`: el argumento de F1 no da `⊥` sin partir de él.
- 🏁🏁🏁 **NINGÚN postulado gödeliano vivo desde el 2026‑09‑10g.** `d3` era la última condición de derivabilidad
  aún postulada. Su prueba real (Σ₁-completitud provable del verificador) es el
  objetivo del plan **12‑A** (`GODEL-D3-TRACKED-DESIGN.md` §12–§14); fases 1a/1b/2
  ✅ completas. `d3` **pasó a teorema** el 2026‑09‑10g y **F7b lo retiró**: quedan **6 axiomas**.

---

## 2 · Meta-reglas de FOL — los 4 `axiom` de `FOL/MetaRules.lean`, REFUTABLES: RPP dejó de importarlas y FOL las borró

✏️ **2026‑10‑02 (ADR‑115).** `imp_intro`, `raa`, `or_elim` y `ex_elim` eran `axiom` de `FOL/MetaRules.lean`, y sus
enunciados se **refutan sin usarlos** (`sondeos/MetaReglasRefutables.lean` §2 y §4; en el build de FOL,
`FOL/Inconsistencia.lean` §3): Lean + cualquiera de ellos demuestra `False`. `gen` y `dne` son constructores de
`Derives` desde D‑2. RPP dejó de importar `FOL.MetaRules` con ADR‑115, y **FOL borró el módulo** el mismo día
(ADR‑115 §8): hoy FOL tiene **0** `axiom` de Lean, como RPP. Lo que sigue es el **registro**
de cómo se describían: «las reglas de deducción de la lógica ω viven en `FOL/MetaRules.lean` y RPP las
re‑exporta desde `Minimal/Axioms.lean`; no cuentan entre los 7 `axiom` de RPP».

| Regla | Rol |
|-------|-----|
| `imp_intro` | Introducción de `⇒` (deducción) |
| `gen` | Generalización ω (`∀n. Γ ⊢ A[n] → Γ ⊢ ∀A`) |
| `raa` | Reducción al absurdo |
| `dne` | Eliminación de doble negación (clásica) |
| `or_elim` | Eliminación de `∨` |
| `ex_elim` | Eliminación de `∃` |

~~Son **reglas del cálculo**, no postulados matemáticos falsables (ADR-008).~~ ✏️ **FALSO** (L1‑3): son
postulados, y están refutados.

---

## 3 · Capa Gödel LEGACY — RETIRADA en F7a (2026-07-09)

Auditado con `#print axioms`, la cadena **real** (entonces `goedel_first_real'`, hoy
**`goedel_first_numeral`** tras la reparación de ADR‑012; `d2_prf`; `goedel_second'`) **no citaba** 🗑️ *(lo que esta línea cita de `⊢` quedó retirado con esa capa, ADR-115)*
ninguno de estos símbolos; solo los usaba la capa
Gödel vieja (Gödel I/II vía D2/D3 postulados). Retirados:

| Símbolo | Estaba en | Reemplazado por (real) |
|---------|-----------|------------------------|
| `Dem`, `dem_iff_provable` | `Meta/Provability.lean` | `HilbertSeq.Dem`/`ProvableH` (concreto) |
| `provFormula`, `provFormula_repr` | `Meta/Provability.lean` | `provCodeC'` + D1 `repr_pos'_prf` |
| `diagonal_lemma` | `Meta/Provability.lean` | hoy **`godelCN_fixedpoint`** (`DiagonalNumeral`) — el `godelC'_fixedpoint` de entonces también murió con ADR‑012 🗑️ *(lo que esta línea cita de `⊢` quedó retirado con esa capa, ADR-115)* |
| `goedelSentence`, `goedelSentence_fixedpoint` | `Meta/Provability.lean` | hoy **`godelCN`** + `godelCN_fixedpoint` 🗑️ *(lo que esta línea cita de `⊢` quedó retirado con esa capa, ADR-115)* |
| `D2` | `Meta/Incompleteness.lean` (**módulo borrado**) | `d2_prf` (`DerivCondPrf`) real |
| `D3` | `Meta/Incompleteness.lean` (**módulo borrado**) | `d3_prf_of_sigma1` (reducido) + plan 12‑A |

El módulo `Meta/Incompleteness.lean` (Gödel I/II legacy completo) se eliminó; sus
teoremas (`goedel_first_unprovable`, `incompleteness`, `con_imp_goedelSentence`, 🗑️ *(lo que esta línea cita de `⊢` quedó retirado con esa capa, ADR-115)*
`goedel_second`; retirados con él en F7a, `f03eacf`) tenían equivalentes reales (`goedel_first_real'`, `goedel_second'`).

---

## 4 · Estado de la cadena real (auditoría 2026-07-09, `#print axioms`)

```text
goedel_first_real'  : [propext, choice, Quot.sound,
                       FOL.MetaRules.{dne, gen, imp_intro},
                       Full.ax_induction, Full.ax_list_induction, ax_axiomsCodeT_eq]
goedel_second'      : [propext, choice, Quot.sound,
                       FOL.MetaRules.{ex_elim, gen, imp_intro, or_elim},
                       Full.ax_list_induction]   -- ⚠️ `d3` YA NO
```

🏁 **Ningún postulado gödeliano** en `goedel_second'` — `d3` retirado el 2026‑09‑10g (F7b CERRADA; era «pendiente de D3»
real).

**Gödel I — precisión (auditoría 2026-07-13):** la mitad **`⊬G`** (`goedel_first_real'`) es **real y
sin postulado gödeliano alguno** ✅. La mitad **`⊬¬G`** (indecidibilidad) **NO está en la cadena real**:
se probó en la capa LEGACY (`Meta/Incompleteness.lean`) apoyándose en `provFormula_repr` —postulado
**bicondicional** cuya dirección `.mp` (representabilidad **negativa**) **no se sigue de la
consistencia simple**—, y se retiró en **F7a** junto con el módulo. **No revertir F7a: fue un arreglo
de solidez.** Para recuperarla honestamente falta construir
`repr_neg : ConsistentOmega → Prf (provCodeC' φ) → Prf φ`. Ver `GODEL-STATUS.md`.

---

## Véase también

- `MINIMAL-AXIOMS.md` — análisis de minimalidad de los 34 axiomas de la **teoría
  objeto** `Minimal` (distinto de las declaraciones `axiom` de Lean listadas aquí).
- `GODEL-D3-TRACKED-DESIGN.md` — plan 12‑A hacia `d3` real (retirada de F7b).
- `CURRENT-STATUS-PROJECT.md`, `REFERENCE.md` §3.17–§3.18 — estado y proyección.

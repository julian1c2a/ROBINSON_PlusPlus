# REFERENCE.md §5 «Próximos pasos» — hasta el 2026‑10‑21 (histórico)

**Last updated:** 2026-10-21 — trasladado TAL CUAL desde `REFERENCE.md` §5 ([ADR‑184](../../DECISIONS.md), T27), que se reescribió desde NEXT-STEPS. Es REGISTRO: el «Hoy» es el del 2026‑10‑04 (ADR‑117) y lo demás, de antes. Lo vigente: `TEOREMAS-E-HIPOTESIS.md` y `NEXT-STEPS.md`. Los enlaces relativos de dentro son los de su documento de origen, en la raíz.

---

Punto de reanudación: **[NEXT-STEPS.md](NEXT-STEPS.md)** (bloque del 2026‑10‑04, ADR‑117). Visión a largo plazo:
[PLANNING.md](PLANNING.md). Libro: [PLAN-LIBRO.md](PLAN-LIBRO.md).

### Hoy (2026‑10‑04, ADR‑117)

🏁 **F1 reparado.** `axiomsCodeT` lo ancla el último de los **142** axiomas objeto, el axioma DIAGONAL
`ax_axiomsCodeT_def` (`Minimal/Axioms.lean`), y `axiomsCodeT =eq listFormCodeM axioms` es el TEOREMA `prf_ancla`
(`Meta/Representability2Prf.lean`); la clase `AnclaEq` se retiró (ADR‑118). Gödel I (`⊬G`) y Gödel II
sobre `Prf` —`goedel_first_prf`, `goedel_second_prf (hcon : ConsistentH)`— ya no llevan `[AnclaEq]`, y su
footprint es el de los tres de Lean: **F1 ya no los hace vacuos**. ⚠️ Siguen **CONDICIONALES**: `ConsistentH`
sólo se cumple si los 142 son consistentes (✏️ desde ADR‑120 lo son: `consistencia`, `Meta/Consistencia.lean`); `f1_traduccion_refutada` bloquea el argumento de F1
(si la traducción conservara el ancla, ya habría `Prf ⊥`; no prueba la consistencia). D1 (`repr_pos'_prf`), D2
(`d2_prf`) y D3 (`d3_prf_real`) ya no llevan ninguna hipótesis de clase (ADR‑118). La mitad `⊬¬G` sigue sin existir
en ningún cálculo. Lo que sigue, en orden: el modelo de los 142 (⇒ `ConsistentH`) ·
`⊬¬G` por **Rosser** · D7 · y el horizonte declarado: Gentzen (ε₀) y Tarski.
✏️ *2026‑10‑14 ([ADR‑134](DECISIONS.md)): este «Hoy» es el del 2026‑10‑04. Después llegaron el modelo y `consistencia`
(ADR‑120), `⊬¬G` (`goedel_I_neg`, ADR‑121, sin Rosser), Tarski (ADR‑121) y D7 (ADR‑129); de esa lista queda Rosser, y
su enunciado está por decidir (T01). La teoría de los titulares, en [AXIOMS.md](AXIOMS.md) §0.*

### 🗄️ Registro del 2026‑10‑02 (ADR‑115; lo de F1, superado por ADR‑117)

⛔ **No hay resultado de incompletitud publicable todavía.** Gödel I (`⊬G`) y Gödel II sobre `Prf`
(`goedel_first_prf`, `goedel_second_prf [AnclaEq] (hcon : ConsistentH)`) están derivados con footprint
de sólo los tres de Lean, pero son **VACUOS**: `[AnclaEq]` da `Prf ⊥` (F1, [ADR‑114](DECISIONS.md)), así
que sus dos hipótesis no pueden valer a la vez. D1 (`repr_pos'_prf`) y D3 (`d3_prf_real`) llevan también
`[AnclaEq]`; D2 (`d2_prf`) no. La mitad `⊬¬G` **no existe en ningún cálculo** desde que se retiró la capa
`⊢` (iba por `NegVerifier`, sobre `⊢`). Lo que sigue, en orden: retirar `MetaRules` en FOL · reparar F1
(L2‑3) · D7 · el modelo de los 141 (⇒ `ConsistentH`) · `⊬¬G` por **Rosser** · y el horizonte declarado:
Gentzen (ε₀) y Tarski.

### 🗄️ Registro del 2026‑09‑10h (superado: lo de abajo describe el árbol de entonces)

**Estado 2026‑09‑10h.** Build **145 jobs**, **131 módulos activos**, **61 `sondeos/`**, 0 sorrys,
**5** `axiom` de Lean (`d3` retirado el 2026‑09‑10g).

### Lo que está cerrado

1. **Gödel I — `⊬G`**: `goedel_first_numeral (hcon : ConsistentOmega) : ¬ Prf godelCN`
   (`Meta/DiagonalNumeral.lean`), sobre el punto fijo real `godelCN_fixedpoint`. Footprint = la base 🗑️ *(lo que esta línea cita de `⊢` quedó retirado con esa capa, ADR-115)*
   sancionada **menos `tc_cons`**.
2. **D1** ✅ `repr_pos'_prf` y **D2** ✅ `d2_prf` — reales, sobre el cálculo finitario `Prf`.
3. **La ESCALERA (a.2)** ✅ **4 de 4** (§3.25): `pcc_eval_add`, `pcc_eval_mul`, el atajo de `div2`, y
   **`pcc_dot_cons`**. Es la Σ₁‑completitud internalizada para argumentos abstractos.

### Los frentes abiertos — **todos MEDIDOS** (actualizado 2026‑09‑10h)

| # | frente | estado | qué lo bloquea |
|--:|---|---|---|
| ~~**1**~~ | ~~muro de `substfc` → `hC_dot` → **D3** → Gödel II → F7b~~ | 🏁🏁 **CERRADO** (2026‑09‑10e/g). Los **7 reflectores** probados ⇒ `pcc_lineWF_tracked` **incondicional** (C3); y **D3 DEMOSTRADA** (`d3_prf_real`) ⇒ `axiom d3` **retirado**, **7 → 6** | — |
| **2** | **`NegVerifier`** → `⊬¬G` | 🏁 **módulo E hecho** (`Meta/VerifierSound.lean`): `verifier_sound` **es** `decodeChain_prf`. 🏁 **[ADR‑022](DECISIONS.md)**: la clase de testigos **estrechada** a `StdLine` ⇒ las comparaciones son **paralelas por tipo, sin evaluar Cantor**. ⚠️ El paso 1.1 del plan (`canon_ne`) sigue siendo **FALSO**, y el sustituto correcto es por **VALOR** (`numTree_ne` + las cotas `consN_ge`/`codeNat_ge`, `archivo/sondeos-2026-10:sondeos/MedirF_Censo.lean`) | **los módulos C y D** — las dos deudas enunciadas `DEUDA_chainNeg` y `DEUDA_inNeg` |
| **3** | **`prf_axiomsCodeT_eq`** 🗑️ *(ese `axiom` quedó retirado el 2026‑09‑12, [ADR‑026](DECISIONS.md): el ancla pasó a la firma como `[AnclaEq]`; desde ADR‑117, 2026‑10‑04, es el teorema `prf_ancla`)* | el axioma que arrastra casi todo el árbol («net‑0 son CUATRO, no tres»). Es de otra naturaleza que los gödelianos: dice que el código de la lista de axiomas **es** la lista de códigos | no medido |
| **4** | 🆕 **`primAxioms`** ([ADR‑023](DECISIONS.md)) | 🏁 **9 de 11 CERTIFICADOS** (2026‑09‑10h). El propietario **ratificó** el movimiento `axiom ax_induction_prim : primAxioms ⊢ inductionFormula φ` + `ax_induction` como **teorema** — **no añade axioma, lo mueve**: siguen **6** | ⬜ los 2 restantes (ax21, ax24) piden una **segunda** sanción sobre `ax_mod2_alternation`, **no pedida**. ⚠️ Antes conviene medir si ese axioma es **derivable** (bajaría a **5**) |
| **5** | **recodificar símbolos por índice** | 📏 medido (`sondeos/RecodCoste.lean`): el **98‑99 %** del `formCode` de los axiomas del verificador son los nombres de símbolos (`ax_tc_zero`: 49 015 → ~708 nodos, **69×**). **Hoy no es cuello de botella** | nada. ⚠️ Una tabla pura **no es total** ⇒ codificación **etiquetada** |

⚠️ **La frase «(1) cuesta axiomas, es decisión del autor» ya NO vale** (era de 2026‑08‑23): el
frente 1 fue por la **vía de CERO axiomas** ([ADR‑015](DECISIONS.md)) y **está cerrado**. La razón
de fondo sigue en §3.27.1: axiomatizar **no era más caro, era OTRO TEOREMA** — sus axiomas entrarían
en `axioms`, `ax_axiomsCodeT_eq` los metería en `axiomsCodeT` y **G cambiaría**. Es la misma 🗑️ *(lo que esta línea cita de `⊢` quedó retirado con esa capa, ADR-115)*
distinción que gobierna [ADR‑023](DECISIONS.md): **certificar sobre un subconjunto no mueve la
frontera; cambiar `axioms` sí**.

### Alternativa siempre disponible *(registro del 2026‑09‑10h; hoy, ver «Hoy» arriba)*

⚠️ Esta sección decía «consolidar **Gödel II módulo el axioma D3**». **Ya no aplica**: `d3` es
teorema desde el 2026‑09‑10g. Lo publicable entonces se creía **más**: Gödel I `⊬G` real sobre la teoría
reparada, **D1, D2 y D3 las tres demostradas**, y Gödel II sin ningún postulado gödeliano —
`goedel_second'` conserva tres hipótesis explícitas que **no** son condiciones de derivabilidad.
Lo único que sigue abierto de Gödel I es la mitad **`⊬¬G`** (frente 2).

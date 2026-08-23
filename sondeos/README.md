# `sondeos/` — experimentos verificados de la sesión 2026‑08‑19

**NO son módulos de producción y NO entran en el build de `lake`** (la `lean_lib` está enraizada en
`ROBINSON_PlusPlus/`; estos ficheros quedan fuera). Se versionan porque **contienen resultados
compilados** que costó obtener y que no deben re‑derivarse.

## Cómo re‑ejecutarlos

```bash
lake env lean sondeos/<fichero>.lean      # desde la raíz de RPP, NUNCA desde FOL/
```

## Qué hay, y qué demostró cada uno

| fichero | sondeo | resultado |
|---|---|---|
| **`DescargaHFN.lean`** | **la comprobación final** | ✅ **EL MÁS IMPORTANTE.** Rehace el piloto con `hFN` **DEMOSTRADA** (vía `Meta/CodeNumeralPrf.lean`). `godelCN_fixedpoint` compila **sin `codeN`, sin `hFN` y sin `tc_cons`**. La vía numeral deja de ser condicional. |
| `PilotoDiagonal.lean` | piloto del lema diagonal (histórico: con `hFN` asumida) | El punto fijo de Gödel **sobrevive** con códigos NUMERALES. `godelCN_fixedpoint` tiene el footprint del original **menos `tc_cons`**. Asume sólo `hFN` (= la salida de S4). Además `provCode_transfer` da la equivalencia con la representación en árbol en **un** paso de Leibniz. |
| **`PilotoRastreada.lean`** | **piloto de la capa RASTREADA** | ⛔ **NEGATIVO, y decide la estrategia.** `prf_cons_eval` permite enfrentar las dos lecturas: `cons 0 nil =eq numeral 2` es demostrable, luego la lectura numeral da `tcFn (cons 0 nil)` con cabeza `⌈σ⌉` y `prf_tc_cons` con cabeza `⌈::⌉`. Son **incompatibles**. La capa rastreada usa `prf_tc_cons` sobre argumentos **ABSTRACTOS** (`pcc_eval_carc (h t)`, `prf_tc_un/bin`), luego **no sobrevive a la reparación**. |
| `S4.lean` | S4 · evaluación de Cantor | Primer eslabón compilado y net‑0: `prf_add_eq_zero_right`. Falta `prf_div2_numeral`. |
| `S3S5.lean` | S3 · simbolismo + S5 · magnitudes | `codeNat` **total y estructural**; 6 teoremas elaboran al instante — Lean **nunca** reduce `codeNat φ`. Y las medidas de S5 (Unicode 19 068 vs índices 45). |
| `PilotoAislado.lean` | fase 2 · familia INVARIANCIA | `substtc_inv_termCode_*` **sin** la lectura sintáctica. Independencia probada por **aislamiento de importaciones**, comprobada por máquina con `#noExiste`. |
| `Magnitud.lean` | S5 · profundidad | `consDepth (formCode ax_tc_succ) = 3873`; log₂(N) de `ax_tc_cons` ≈ 8,66 × 10⁷⁸. |
| `S1Audit.lean` | S1 · auditoría | ⚠️ **Sólo compila en la rama `sondeo/s1-sin-ax-tc-cons`** (necesita `prf_tc_cons`/`tc_cons` como axiomas de Lean). En `master` no. |
| **`CanonNeRefuta.lean`** | **`NegVerifier` · refutación de `canon_ne`** | ⛔ **NEGATIVO, y decide el frente.** El paso **1.1** de `PLAN-NEGVERIFIER.md` (base de los módulos C y D) es **FALSO**: `cons nil nil = 2 = numeralM 2` son distintos en Lean y **provablemente iguales** en la teoría, así que `canon_ne` daría `⊥`. El plan es de **julio, anterior a la inconsistencia**, y arrastra el **mismo error de categoría**. Salida: pasar a **numerales**, como ADR‑012. |
| `KitPayoff.lean` | (paso 4) · **medición del KIT** | ✅ **NO es un muro.** `pcc_dot_nul`/`_un`/`_bin` salen **por composición de `pcc_dot_cons`, sin inducción nueva** (nul: sólo código; un: 1 paso interno; bin: 2 anidados). Hizo falta `pcc_dot_cons_symm`, vía `pcc_eq_symm_code_internal` — que volvió con `BdAllIntroPrf` en el paso 3. ⚠️ **El coste real no está en el KIT sino en `CodeTreeReflect`**: `prf_tc_objAt` es recursión sobre `CTree` que hay que mover entera dentro de `Prov`. Todas las piezas existen (`pcc_eq_trans_code` + las congruencias internas del KIT, que **sobreviven**). |
| `TcFormPayoff.lean` | (paso 3) · **medición de `prf_tc_form`** | ✅ **NO es un muro.** El sustituto directo es una línea y net‑0, pero el lado derecho (`termCode (formCode φ)`) **no es negociable**: `inDot` está fijado por `D3DottedPrf`, activo y net‑0, y ese código **es el objetivo de D3**. La salida: **D1 dota `prf_formCode_numeral`** y da el puente entre las dos formas DENTRO de `Prov` ⇒ `pcc_to_formCode`/`_imp`. **Estrategia: no tocar definiciones, convertir en la frontera.** |
| `CarcPayoff.lean` | (a.2) · **el rédito de `pcc_dot_cons`** | ✅ **`pcc_eval_carc` RECUPERADO**, mismo enunciado y mismo footprint. El viejo (`cuarentena/EvalListPrf.lean:123`) cerraba con `prf_tc_cons'` — el puente que murió con la reparación; la sustitución es **un único `pcc_rw` con `pcc_dot_cons`**, y los pasos 1‑3 quedan intactos. Confirma que el keystone `EvalListPrf` es repatriable. |

## ⚠️ Dos trampas metodológicas aprendidas hoy (no repetir)

1. **La alcanzabilidad por `import` da FALSOS NEGATIVOS.** Concluí que Gödel I estaba limpio porque
   `DiagonalTwo` no alcanza `TcArithPrf`; se me escapó `Meta/Diagonal.lean`, que tiene el mismo
   puente en la capa ω. **Sólo `#print axioms` es concluyente.**
2. **Un crawler de dependencias transitivas tampoco sirve**: Lean 4.31 devuelve `value? = NONE`
   para teoremas importados, así que sólo recorre **tipos**, no pruebas. Medido.
   **La técnica que SÍ funciona** es la de `S1Audit`: convertir el puente sospechoso en **`axiom` de
   Lean** y dejar que `#print axioms` delate a sus consumidores.

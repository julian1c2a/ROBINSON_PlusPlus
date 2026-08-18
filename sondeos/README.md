# `sondeos/` — experimentos verificados de la sesión 2026‑07‑27

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

## ⚠️ Dos trampas metodológicas aprendidas hoy (no repetir)

1. **La alcanzabilidad por `import` da FALSOS NEGATIVOS.** Concluí que Gödel I estaba limpio porque
   `DiagonalTwo` no alcanza `TcArithPrf`; se me escapó `Meta/Diagonal.lean`, que tiene el mismo
   puente en la capa ω. **Sólo `#print axioms` es concluyente.**
2. **Un crawler de dependencias transitivas tampoco sirve**: Lean 4.31 devuelve `value? = NONE`
   para teoremas importados, así que sólo recorre **tipos**, no pruebas. Medido.
   **La técnica que SÍ funciona** es la de `S1Audit`: convertir el puente sospechoso en **`axiom` de
   Lean** y dejar que `#print axioms` delate a sus consumidores.

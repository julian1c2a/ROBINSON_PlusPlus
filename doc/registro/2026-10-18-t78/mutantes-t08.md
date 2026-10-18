# T08 visto fallar con los corolarios de T78: dos mutantes (2026-10-18, ADR-162)

**Last updated:** 2026-10-18 — registro (ADR‑162): la salida de los dos mutantes, tal cual. Lo que dice del árbol es de
esa fecha; no se actualiza.

**Qué.** `prf_godel_iff_con` y `goedel_second_formalizado` entran en `PUROS` (`Meta/PurezaTitulares.lean`). Como con
Rosser y Löb, el control se vuelve a ver fallar con mutantes de este uso. La fuente, en
[`MutanteT78.lean.txt`](MutanteT78.lean.txt); se lanzó con `lake env lean`, desde la raíz de RPP, sobre el build de
ADR‑162 (131 jobs).

* **M1:** `con_indecidible`, que usa la verdad en `MNV V₀`, declarado PURO.
* **M2:** `prf_godel_iff_con` declarado control positivo: no nombra la semántica, así que tiene que decir «CIEGO».

La salida tiene exactamente los dos errores de T08 y ninguno de elaboración.

## La salida (código de salida 1)

```
MutanteT78.lean:6:0: error: ⛔ T08 · el control de pureza FALLA (ADR‑143):
  ROBINSON_PlusPlus.Meta.GodelCorolarios.con_indecidible nombra la semántica:
      ROBINSON_PlusPlus.Meta.GodelCorolarios.con_indecidible ⟶ FOL.Metamath.Semantics.evalFormula
MutanteT78.lean:9:0: error: ⛔ T08 · el control de pureza FALLA (ADR‑143):
  ROBINSON_PlusPlus.Meta.GodelCorolarios.prf_godel_iff_con NO nombra la semántica, y TIENE que nombrarla (llama a `consistencia`): el criterio está CIEGO
```

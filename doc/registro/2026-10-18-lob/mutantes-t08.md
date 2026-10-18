# T08 visto fallar con Löb: tres mutantes (2026-10-18, ADR-159)

**Last updated:** 2026-10-18 — registro (ADR‑159): la salida de los tres mutantes, tal cual. Lo que dice del árbol es
de esa fecha; no se actualiza.

**Qué.** `lob` entra en `PUROS` (`Meta/PurezaTitulares.lean`). Como con Rosser (`../2026-10-18-rosser/`), el control
se vuelve a ver fallar con mutantes de este uso.

**Cómo se lanzó.** `lake env lean <scratchpad>/MutanteLob.lean`, desde la raíz de RPP, sobre el build de ADR-159
(140 jobs). La fuente, tal cual, en [`MutanteLob.lean.txt`](MutanteLob.lean.txt).

* **M1:** `control_reflexion_bot`, que descarga la consistencia con `consistencia`, declarado PURO.
* **M2:** `lob` declarado control positivo: no nombra la semántica, así que el control tiene que decir «CIEGO».
* **M3:** el enunciado de `lob` con una prueba que NOMBRA `prf_sound` en el modelo estándar (un `have` que la prueba no
  usa), declarado PURO. Comprueba que T08 ve la mención, no una ruta por el modelo.

La salida tiene exactamente los tres errores de T08 y ninguno de elaboración (la lección del primer intento de Rosser:
un mutante que no compila no mide nada).

## La salida (código de salida 1)

```
MutanteLob.lean:8:0: error: ⛔ T08 · el control de pureza FALLA (ADR‑143):
  ROBINSON_PlusPlus.Meta.Lob.control_reflexion_bot nombra la semántica:
      ROBINSON_PlusPlus.Meta.Lob.control_reflexion_bot ⟶ ROBINSON_PlusPlus.Meta.Consistencia.consistencia ⟶ ROBINSON_PlusPlus.Meta.SolidezPrf.consistentH_de
MutanteLob.lean:11:0: error: ⛔ T08 · el control de pureza FALLA (ADR‑143):
  ROBINSON_PlusPlus.Meta.Lob.lob NO nombra la semántica, y TIENE que nombrarla (llama a `consistencia`): el criterio está CIEGO
MutanteLob.lean:19:0: error: ⛔ T08 · el control de pureza FALLA (ADR‑143):
  mutanteSolidez nombra la semántica:
      mutanteSolidez ⟶ ROBINSON_PlusPlus.Meta.SolidezPrf.prf_sound
```

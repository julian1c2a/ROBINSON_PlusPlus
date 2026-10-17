# T08 visto fallar con Rosser: tres mutantes (2026-10-18, ADR-157)

**Qué.** `rosser_ext` entra en `PUROS` y `rosser` en `IMPUROS` (`Meta/PurezaTitulares.lean`). Un control reutilizado se
vuelve a ver fallar: estos tres mutantes TIENEN que hacer fallar a `#pureza`, y lo hacen.

**Cómo se lanzó.** `lake env lean <scratchpad>/MutanteRosser.lean`, desde la raíz de RPP, sobre el build de ADR-157
(139 jobs). La fuente, tal cual, en [`MutanteRosser.lean.txt`](MutanteRosser.lean.txt): `.lean.txt` para que ni Lake ni
ningún control la tome por módulo.

* **M1:** `rosser`, que descarga la hipótesis con `consistencia`, declarado PURO.
* **M2:** `rosser_ext` declarado control positivo: no nombra la semántica, así que el control tiene que decir «CIEGO».
* **M3:** el enunciado de `rosser_ext` con una prueba que NOMBRA `prf_sound` en el modelo estándar, la raíz de la ruta de
  `sondeos/RosserReflexion.lean`, declarado PURO. Es lo más cerca que se puede llegar del mutante que pedía T01 («visto
  fallar con un mutante que pase por RosserReflexion»): el sondeo no se puede importar. Pero M3 sólo comprueba que T08
  ve la mención de `prf_sound` (un `have` que la prueba no usa), no que la ruta de la reflexión se recorra.

## La salida (código de salida 1)

```
MutanteRosser.lean:8:0: error: ⛔ T08 · el control de pureza FALLA (ADR‑143):
  ROBINSON_PlusPlus.Meta.Rosser.rosser nombra la semántica:
      ROBINSON_PlusPlus.Meta.Rosser.rosser ⟶ ROBINSON_PlusPlus.Meta.Consistencia.consistencia ⟶ ROBINSON_PlusPlus.Meta.SolidezPrf.consistentH_de
MutanteRosser.lean:11:0: error: ⛔ T08 · el control de pureza FALLA (ADR‑143):
  ROBINSON_PlusPlus.Meta.Rosser.rosser_ext NO nombra la semántica, y TIENE que nombrarla (llama a `consistencia`): el criterio está CIEGO
MutanteRosser.lean:22:0: error: ⛔ T08 · el control de pureza FALLA (ADR‑143):
  mutanteReflexion nombra la semántica:
      mutanteReflexion ⟶ ROBINSON_PlusPlus.Meta.SolidezPrf.prf_sound
```

## ⚠️ El primer intento de M3 midió NADA

La primera versión de M3 escribía `FOL.Formula`, que no existe. Con el cuerpo en error, Lean añadió la declaración con
lo que pudo elaborar, sin la llamada a `prf_sound`, y `#pureza` la dio PURA («✓ PURO mutanteReflexion (359 constantes
del proyecto en el cierre)»). Un mutante que no compila no mide nada, y da el resultado que se espera de un titular
bueno. Corregidos los nombres (`open FOL`, `Formula`), falla como debe. Por eso aquí va la salida de la versión que
compila, y la fuente es esa.

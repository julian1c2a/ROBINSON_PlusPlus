# Inventario de NegNum y PosNum (2026‑10‑16)

**Last updated:** 2026-10-16 — registro de ADR‑146 (el diseño de NegNum y PosNum de T). Es REGISTRO: lo que dice del
árbol es de esa fecha (HEAD `24e3b55`); no se actualiza.

| fichero | qué es | origen |
|---|---|---|
| `pureza.txt` | las 92 piezas que el plan de Rosser y los inventarios nombran, clasificadas por el recorrido de T08: 76 PURAS, 4 IMPURAS (W1, por `linea_thy` → `V₀_eq_codigo`) y 12 FUERA del build (viven en sondeos) | `sondeos/InventarioRosser.lean` (23 s) |
| `inventario-plan.md` | el plan de Rosser (Etapas 0–7, `resultado.json` de ADR‑122) y su estado, con las cifras citadas tal cual y los riesgos | un agente de sólo lectura |
| `inventario-posnum.md` | lo que existe para PosNum (D1, `proofCode'`, la evaluación a numeral) y lo que falta | un agente de sólo lectura |
| `inventario-negnum.md` | lo que existe para NegNum (las guardas, `ChainNegPrf`, los refutadores, la decisión de numerales) y lo que falta, por subobjetivo | un agente de sólo lectura |

Los tres inventarios son los informes finales de los agentes, condensados (las citas, las cifras y las referencias fichero:línea, tal cual): leyeron el árbol y no compilaron nada. Sus
etiquetas son [R]/READ (leído en el fuente), [T] (comprobado ese día en el código) e [I]/INFERRED (inferencia suya).
Las clasificaciones de pureza de `pureza.txt` sí están MEDIDAS (compilado).

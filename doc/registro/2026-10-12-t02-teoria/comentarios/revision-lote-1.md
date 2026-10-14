# Revisión adversarial del lote de comentarios · parte 1

**Last updated:** 2026-10-14 — registro (ADR‑134): copia tal cual de lo que se produjo ese día; no se actualiza. La marca está para el control `[E]` de `check-doc-sync.bash`, que mira todo `.md` versionado.

> Registro: el informe final de un agente de sólo lectura, tal cual (fecha: 2026-10-14). Lo que dice del árbol es de esa fecha; lo aplicado, en ADR-134.

Encontré **16 defectos en 11 sitios**: uno falso (A), uno inexacto (M) y catorce menores (m). Siete de los menores son punteros `fichero:línea` que el propio lote desplazó. Todo es sólo lectura: no edité nada ni ejecuté lake, lean ni leanchecker.

## Defectos

**1. `ROBINSON_PlusPlus/Minimal/Axioms.lean:350‑351` — A (falso)**
- Frase: «`mod2_of_even` pasó a Block4_C6_C7 el 2026‑06‑03 y, al retirarse con la capa `⊢` —ADR‑115—, no tenía `sorry`: no queda nada pendiente.»
- Por qué es falsa:
  - Que no tenía `sorry` es cierto, pero ese `mod2_of_even` era una «instancia directa de ax24» (`git show b1dedd1^:ROBINSON_PlusPlus/Minimal/Theorems/Block4_C6_C7.lean`, líneas 136‑146): no derivaba nada.
  - La derivación de `ax24` desde los primitivos era `mod2_of_even_prim` (`b1dedd1^:Full/Mod2.lean:286`), sobre `⊢`, y se retiró con ADR‑115.
  - Hoy no hay ninguna derivación: `Full/Induction.lean:54‑56` y `:74‑76` dicen que no hay certificado de los 10 derivables, `ax24` entre ellos. Ningún `prf_*` usa `ax24` (grep).
  - Lo «pendiente» —que sea teorema en un sistema con inducción— sigue pendiente.
- Reemplazo: «… y no tenía `sorry`, pero era una instancia de este mismo axioma; la derivación de `ax24` por inducción fue `mod2_of_even_prim` (`Full/Mod2.lean`, sobre `⊢`), retirada con ADR‑115, y hoy no hay ninguna, tampoco sobre `Prf` (ver `primAxioms` en `Full/Induction.lean`).»

**2. `Minimal/Axioms.lean:1598‑1599` — M (inexacto)**
- Frase: «`premsOf`, sólo sobre las líneas con la forma de su regla —etiqueta y longitud—, que son las que cumplen `lineWF`».
- Por qué: los `ax_premsOf_*` (`:1407`, `:1434`, `:1455`…) valen para toda línea explícita con esa etiqueta y esa longitud, cumpla o no `lineWF`. `lineWF` exige además la ecuación de la conclusión (`ax_lineWF_p1`, `:1449‑1453`). Implica la forma, pero la forma no implica `lineWF`.
- Reemplazo: «… —etiqueta y longitud—, entre ellas todas las que cumplen `lineWF` (que fija la longitud); una línea con etiqueta conocida y otra longitud no tiene ecuación».

**3. `Minimal/Axioms.lean:1695` — m**
- Frase: «desde el 2026‑06‑03 estaba en Block4_C6_C7, y al retirarse no tenía `sorry`».
- Por qué: es cierto, pero al lado de «teorema en sistemas con inducción» sugiere que `mod2_of_even` era ese teorema.
- Reemplazo: «… sin `sorry` pero como instancia de ax24; hoy no hay derivación de ax24 (ver la nota de su definición)».

**4. `Minimal/Axioms.lean:110` — m**
- Frase: «$π₁(x,y) = …$».
- Por qué: la fórmula ya está bien, pero `π₁` denota la primera proyección, no el emparejamiento.
- Reemplazo: «$\text{pair}(x,y) = \frac{(x+y)(x+y+1)}{2} + y$».

**5. `Meta/ChainNegPrf.lean:149` — m, puntero roto por este lote**
- Frase: «(`Meta/RunFnBoundedPrf.lean:225` y `:246`)», en el mismo párrafo que la nota nueva.
- Por qué: las 5 líneas añadidas hoy a `RunFnBoundedPrf` desplazaron los teoremas a `:230` y `:251`. En el índice estaban en 225 y 246.
- Reemplazo: «(`prf_In_runFn_of_boundedCarcIn` y `prf_boundedCarcIn_of_In_runFn`, `Meta/RunFnBoundedPrf.lean`)».

**6. `Meta/EvalSubsttcPrf.lean:746` — m**
- Frase: «Este fichero abre `Sigma1AtomPrf` en la línea 17».
- Por qué: el `open` está en `:56`. El autor quitó los otros dos números de línea del párrafo y dejó éste, que ya era falso.
- Reemplazo: «Este fichero abre `Sigma1AtomPrf` (el `open` de la cabecera)».

**7. `Meta/VerifierSound.lean:48` — m**
- Frase: «registro; se midió sobre `⊢`…».
- Por qué: llamarlo «registro» sugiere que la discrepancia ya no existe, y sigue sobre `Prf`: `prf_lineWF_p1` (`Meta/ReprPrf.lean:543`) no lleva guardas.
- Reemplazo: «(✏️…: se midió sobre `⊢`, retirado con ADR‑115, y `sondeos/NegVerifierModE.lean` ya no compila; sobre `Prf` la discrepancia sigue: `prf_lineWF_p1` vale para códigos arbitrarios)».

**8. `Meta/OmegaReflect.lean:49‑50` — m**
- Frase: «sin este módulo, que no importa».
- Por qué: se lee como «que no tiene importancia». El hecho es cierto: el cierre de imports de `SolidezVerificador` no lo contiene.
- Reemplazo: «… sin este módulo, que `SolidezVerificador` no importa».

**9. `Meta/DerivCondPrf.lean:26` — m**
- Frase: «(D2 ω-level, sobre `⊢`; …)».
- Por qué: la línea editada conserva «ω-level», y `gen` no es la ω‑regla (ADR‑027). El lote corrigió ese mismo error en `NatOrderPrf`, `OmegaReflect` y `CodeNatInjPrf`.
- Reemplazo: «(D2 sobre `⊢`; retirado, ADR‑115)».

**10. `ROBINSON_PlusPlus.lean:15` — m**
- Frase: «GODEL-STATUS.md es histórico».
- Por qué: su banner (`GODEL-STATUS.md:3‑10`, del 2026‑10‑05) está al día. Es histórico el cuerpo (`:74`).
- Reemplazo: «GODEL-STATUS.md es histórico salvo su banner».

**11. `Meta/HilbertSeq.lean:42` — m**
- Por qué: hoy se cambió el contenido de una nota fechada «2026‑10‑13» sin cambiar la fecha, y la línea pasa de 150 columnas.
- Arreglo: añadir «; ampliada el 2026‑10‑14» y partir la línea.

**12. `Meta/Consistencia.lean:50‑51` y `Full/Induction.lean:238‑239` — m, cosmético**
- `Consistencia`: «(✏️» queda al final de una línea y la fecha en la siguiente.
- `Induction`: la nota parte en dos el título `### …`, que se trunca al renderizar. Basta poner la nota en una línea propia bajo el título.

**13. Punteros rotos fuera de los ficheros del lote — m**
Los ficheros del lote crecieron y estos punteros quedaron desplazados:
- `Meta/CodeWitnessPrf.lean:114`: «`NumCodeClosedPrf.lean:53`». `prf_congr_liftc` está hoy en `:57`.
- `Meta/CodeNumeralPrf.lean:123`: «`Provability.lean:34-63`». Hoy el tramo es `:38‑67`.
- `Meta/D3ChainDotPrf.lean:36`: «`Minimal/Axioms.lean:865`». `def chainOk` está hoy en `:884`. Ya estaba roto en el índice (`:874`), por las ediciones de ADR‑134 del 10‑12.
- `sondeos/S3S5.lean:42` («`Provability.lean:55‑63`») y `sondeos/ClassicalChoiceCenso.lean:67` («`Provability.lean:39`»).
- Arreglo: citar por símbolo (`prf_congr_liftc`, `charsCode`…`formCode`, `chainOk`).

## Lo que se sostiene

Comprobé unas 125 afirmaciones; se sostienen unas 111. Entre ellas:
- los nombres, firmas y guardas citados;
- los commits `01ef473`, `0651c1e`, `5891d06`, `0bca4ed` y `9a608c9`, y la fecha de F7a;
- los cierres de imports (`SolidezVerificador` no importa `ChainNegPrf`, `OmegaReflect` ni `VerifierSound`);
- los consumidores (`decodeForm_inj` sólo lo usa `decodeLine_carc`; `PrfH_w1` no lo usa nadie; los seis módulos que usan la monotonía de Cantor);
- las cifras: 11 constructores de `NotFC`, 7 declaraciones de `CodeDistinct`, 35 símbolos −2 = 33, los 8 tags de `decodeForm`, los cinco sondeos con rc 1.

La sintaxis está limpia: el número de `/-` y `-/` de cada fichero es igual en el índice y en el árbol, ninguna línea `+` deja un acento grave desemparejado, y todos los ficheros conservan CRLF.

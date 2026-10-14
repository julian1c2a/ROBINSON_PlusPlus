# Corrección de comentarios · grupo 1a (raíz, barriles, Minimal, Gödel)

**Last updated:** 2026-10-14 — registro (ADR‑134): copia tal cual de lo que se produjo ese día; no se actualiza. La marca está para el control `[E]` de `check-doc-sync.bash`, que mira todo `.md` versionado.

> Registro: el informe final de un agente de sólo lectura, tal cual (fecha: 2026-10-14). Lo que dice del árbol es de esa fecha; lo aplicado, en ADR-134.

Hecho: de los 30 hallazgos del grupo 1a, 28 llevan texto nuevo (corrección o nota) y 2 se omiten porque una marca existente ya los cubre. No he rechazado ninguno. Hay 1 hallazgo NUEVO en mis ficheros y 2 fuera de mi lista, que no he tocado. Sólo he tocado comentarios: nada de lake/lean, y git sólo de lectura.

Los números de línea son los de después de editar. Todas las fechas y ADR nuevas llevan U+2011. Ninguna línea añadida mete `/-` ni `-/` nuevos, y no aparece `prf_axiomsCodeT_eq`.

## Raíz y barriles

**1a‑01** · `ROBINSON_PlusPlus.lean:14‑16` · NOTA (A). Evidencia: `GODEL-STATUS.md:74` se declara «DOCUMENTO HISTÓRICO» y remite a NEXT‑STEPS/AXIOMS. Texto nuevo, bajo la línea 13:
`-- (✏️ 2026‑10‑14, ADR‑134: hoy también el Nivel D sobre `Prf` —D1–D3, el modelo `MNV V₀`, `consistencia`,` / `-- Gödel I entero y Gödel II sin hipótesis, Tarski—; GODEL-STATUS.md es histórico: el estado vivo, en` / `-- NEXT-STEPS.md y AXIOMS.md §0.)`

**1a‑02** · CORREGIDO (B): la frase es del 2026‑10‑02 (b1dedd1), y `listInd` existe desde el 2026‑06‑24 (9a52dee). Evidencia: `Meta/Hilbert.lean:158` y la tabla de `AXIOMS.md` §0.3 (D2, D3 y Gödel II usan `listInd`).
- `ROBINSON_PlusPlus.lean:21‑22`: «…La inducción de la cadena entra por los constructores `Prf.ind` y / `Prf.listInd` (Meta/Hilbert.lean; ✏️ 2026‑10‑14: decía «es el constructor `Prf.ind`»; AXIOMS.md §0.3).»
- `Full/Induction.lean:35‑38`: «Hoy la inducción de la cadena de Gödel entra por los constructores `Prf.ind`, que usa la `inductionFormula` de abajo, y `Prf.listInd` (la de listas, `listInductionFormula`, en `Meta/Hilbert.lean`; ✏️ 2026‑10‑14: decía «es el constructor `Prf.ind`»; `AXIOMS.md` §0.3); de este módulo quedan…»

**1a‑03** · `Full/Induction.lean:50‑51` · NOTA (A). Evidencia: `primAxioms_len : primAxioms.length = 24`. El título es de e559392 (2026‑09‑10, 19:23) y la lista pasó a 24 en 4aaf12e (21:40). Texto nuevo, bajo el título: «✏️ 2026‑10‑14 (ADR‑134): son **24** primitivos y 10 derivables (`primAxioms_len`) desde la tarde del mismo 2026‑09‑10, cuando `ax21` resultó primitivo (ver el docstring de `primAxioms_len`); el título es de antes.»

**1a‑04** · NOTA (A), en dos sitios:
- `Full/Induction.lean:76‑78`: «(✏️ 2026‑10‑14, ADR‑134: «`Full`», la teoría `Minimal` + `ax_induction` sobre `⊢`, ya no existe; la teoría con inducción es hoy la de `Prf`, `T_Prf`: `AXIOMS.md` §0.)»
- `Full/Induction.lean:238‑239`, en el título: «(✏️ 2026‑10‑14, ADR‑134: hoy no es un axioma, sino la fórmula del constructor `Prf.ind`)». Evidencia: `inductionFormula` es un `def`, y `Prf.ind` la usa (`Hilbert.lean:156`).

**1a‑05** · `Meta.lean:20‑22` · NOTA (A), viñeta nueva en la API. Evidencia: `Consistencia.lean:50/53/57`, `SolidezVerificador.lean:558/572`, `TarskiPrf.lean:94/131`. Texto: «· ✏️ 2026‑10‑14 (ADR‑134), sin hipótesis: `consistencia`, `goedel_I`, `goedel_II` (Meta/Consistencia.lean, ADR‑120); `goedel_I_neg` y `godelCN_indecidible` (Meta/SolidezVerificador.lean, ADR‑121: Gödel I entero); `tarski`, `tarski_semantico` (Meta/TarskiPrf.lean, ADR‑121).»

**1a‑06** · `Meta.lean:17‑19` · CORREGIDO (B). Evidencia: `ConsistentH := ¬ Prf ⊥` (`Hilbert.lean:173`). Texto: «🏁 La consistencia de `T_Prf` —los 142 con los esquemas de `Prf`— está probada desde ADR‑120 (`consistencia : ConsistentH`: `MNV V₀`, un modelo estándar de los 142, y `prf_sound`; ✏️ 2026‑10‑14: decía «La consistencia de los 142»).»

**1a‑07** · `Meta.lean:27‑28` · NOTA (A). Evidencia: `SolidezVerificador.lean:558`. Texto: «(✏️ 2026‑10‑14, ADR‑134: la mitad `⊬¬G` volvió, sobre `Prf`, con ADR‑121: `goedel_I_neg`, por la solidez del verificador en `MNV V₀`.)»

## Minimal/Axioms.lean

**1a‑10** · `:108‑112` · CORREGIDO (B). Evidencia: `cantor_poly` = `(x+y)(x+y+1)+2y`, `cantor_func` = `div2 (cantor_poly …)`, `pair` = `cantor_func`. Texto nuevo:
«$π₁(x,y) = \frac {(x+y)(x+y+1)} {2} + y$
(✏️ 2026‑10‑14: decía «$π₁(x,y) = \frac { \frac {(x+y)(x+y+1)} {2} + y } {2}$», que divide dos veces, y daba un «$π₂(x,y) = \frac { \frac {(x+y)(x+y+1)} {2} + y } {2} - (π₁(x,y) * 2)$» que no corresponde a nada del código: `pair` es `cantor_func` = `div2 (cantor_poly x y)` = $\frac {(x+y)(x+y+1) + 2y} {2}$, y $(x+y)(x+y+1)$ es par.)»

**1a‑11** · NOTA (A) en cinco sitios. Evidencia: un grep en `ROBINSON_PlusPlus/`, `sondeos/` y `../FOL` no encuentra ningún `proj1`, `proj2`, `x_of_c`, `y_of_c` ni `proj_is_cantor` fuera de comentarios. `Block4_C6_C7` y `Block4_C5` se borraron en b1dedd1 (ADR‑115); en `b1dedd1^`, `Block4_C6_C7.lean:128/134/153` los definía.
- `:55‑56`: «(✏️ 2026‑10‑14, ADR‑134: Block4_C6_C7 se retiró con la capa `⊢`, ADR‑115, y con él proj1/proj2, x_of_c, y_of_c y proj_is_cantor: hoy no existe ninguno.)»
- `:89‑90`: «(✏️ 2026‑10‑14, ADR‑134: retiradas con Block4_C6_C7, ADR‑115; ver arriba.)»
- `:340`: «-- (✏️ 2026‑10‑14, ADR‑134: Block4_C6_C7 se retiró con ADR‑115; ni esas defs ni `proj_is_cantor` existen hoy.)»
- `:361`: «-- (✏️ 2026‑10‑14, ADR‑134: Block4_C5 y esas pruebas, sobre `⊢`, se retiraron con ADR‑115.)»
- `:1693`: «…como teorema `proj_is_cantor` (retirados, ADR‑115).», con el estilo de sus vecinas.

**1a‑12** · `:350‑351` · NOTA (A): «sorry pendiente» es del 2026‑05‑11. Evidencia: `Block5.lean:44` (en `b1dedd1^`) dice que `mod2_of_even` se movió a Block4_C6_C7 el 2026‑06‑03, y ese fichero, al retirarse, tenía 0 `sorry`. Texto: «-- (✏️ 2026‑10‑14, ADR‑134: `mod2_of_even` pasó a Block4_C6_C7 el 2026‑06‑03 y, al retirarse con la capa `⊢` / -- —ADR‑115—, no tenía `sorry`: no queda nada pendiente.)»

**1a‑13** · `:587` · NOTA (A): la frase es del 2026‑06‑17, antes de que existieran las etiquetas 18‑20. Evidencia: `ax_vpf_ind` / `ax_vpf_qconf` / `ax_vpf_listInd`, con `numeralM 18/19/20`. Texto: «-- (✏️ 2026‑10‑14, ADR‑134: hoy las etiquetas son 0..20: 18 = `ind` (`ax_vpf_ind`), 19 = `qconf`, 20 = `listInd`.)»

**1a‑14** · `:911‑914` · NOTA (A). Evidencia: la lista `axioms` (`:1657`) lleva `ax_tc_zero` y `ax_tc_succ`, y `ax_tc_cons` está comentada; `control_tc_cons` en `ModeloCodificacion.lean:391`; `prf_godelCN_fixedpoint`; `prf_diagonal` en `TarskiPrf.lean:49`.
- He citado el punto fijo y `prf_diagonal`, no `prf_ancla` como sugería el verificador: la frase habla del código del código del lema diagonal, no del ancla.
- Texto: «(✏️ 2026‑10‑14, ADR‑134: de las 3 ecuaciones, la lista `axioms` lleva 2, `ax_tc_zero` y `ax_tc_succ`: `ax_tc_cons` está fuera desde ADR‑012, y el modelo la refuta, `control_tc_cons`; y la diagonalización ya no falta: el punto fijo es `prf_godelCN_fixedpoint` (`Meta/GodelTwoPrf.lean`), y el lema diagonal general, `prf_diagonal` (`Meta/TarskiPrf.lean`).)»

**1a‑15** · `:174` · CORREGIDO (puntero; las definiciones están en `:472` y `:918`). Texto: «`forall_4` (junto a `substtc`) y `forall_5` (tras `ax_tc_cons`)».

## Meta/

**1a‑20** · `Consistencia.lean:49‑51` · CORREGIDO (B). Evidencia: `estandar_MN` (`:43`), `consistentH_de`, `prf_sound`. Texto: «🏁 **`T_Prf` es CONSISTENTE** (los 142 con los esquemas de `Prf`): `Prf ⊥` no tiene prueba, porque `MNV V₀` es estándar y satisface los 142 (`estandar_MN`), y `Prf` es sólido en todo modelo estándar (`prf_sound`). (✏️ 2026‑10‑14: decía «Los 142 son CONSISTENTES… porque `MNV V₀` satisface los 142 (`MN_axioms`)».)»

**1a‑21** · `GodelTwo.lean:47‑49` · NOTA (A). Evidencia: `Consistencia.lean:57`. Texto: «(✏️ 2026‑10‑14, ADR‑134: y desde ADR‑120 va sin hipótesis: `goedel_II : ¬ Prf consistencyFormula'`, en `Meta/Consistencia.lean`, es `goedel_second_prf consistencia`.)»

**1a‑22** · `GodelTwo.lean:116‑119` · OMITIDO: ya lo cubre la nota ✏️ 2026‑10‑12 de T02 (índice), «desde ADR‑120 está probada —`consistencia : ConsistentH`…— … `T_Prf`».

**1a‑23** · `GodelTwoPrf.lean:202‑204` · NOTA. Evidencia: `AXIOMS.md` §0.3, fila de `goedel_second_prf`/`goedel_II` (ind sí, listInd sí). Texto: «(✏️ 2026‑10‑14, ADR‑134: desaparecen los `axiom`, no la inducción: Gödel II construye pasos con `Prf.ind` y `Prf.listInd`, constructores de `Prf` que `#print axioms` no ve; `AXIOMS.md` §0.3.)»

**1a‑24** · `DiagonalNumeral.lean:54‑56` · NOTA (A): un «hoy» del 2026‑10‑04. Evidencia: `goedel_I_neg` usa `prf_godelCN_fixedpoint` (`SolidezVerificador.lean:560‑561`). Texto: «(✏️ 2026‑10‑14, ADR‑134: y `ConsistentH` es un teorema desde ADR‑120: `goedel_I`, sin hipótesis, en `Meta/Consistencia.lean`; esa misma forma la consume `goedel_I_neg`, `Meta/SolidezVerificador.lean`.)»

**1a‑25** · `DiagonalTwo.lean:99‑101` · NOTA (A). Evidencia: `SolidezVerificador.lean:558`. Texto: «(✏️ 2026‑10‑14, ADR‑134: la mitad `⊬¬G` sí la tiene hoy, `goedel_I_neg` (`Meta/SolidezVerificador.lean`, ADR‑121), por la solidez del verificador en `MNV V₀`; Rosser —⊬R ∧ ⊬¬R sólo con `ConsistentH`— sigue ⬜.)»

**1a‑26** · NOTA (A), en dos sitios. Evidencia: `SolidezVerificador.lean:572‑574`.
- `DiagonalTwo.lean:53‑55`: «> (✏️ 2026‑10‑14, ADR‑134: hoy Gödel I va / > entero y sin hipótesis: `goedel_I` (`Meta/Consistencia.lean`) y `goedel_I_neg`, juntos en / > `godelCN_indecidible` (`Meta/SolidezVerificador.lean`).)»
- `DiagonalTwo.lean:92`: «-- (✏️ 2026‑10‑14, ADR‑134: y entero y sin hipótesis, `godelCN_indecidible`: ver la nota de arriba.)»

**1a‑27** · `Provability.lean:26‑28` · NOTA (A): el título es del 2026‑06‑06 (fccc162). Evidencia: el `export` del módulo sólo tiene codificación. Texto: «✏️ 2026‑10‑14 (ADR‑134): el título es del 2026‑06‑06. Hoy el módulo sólo tiene la codificación (`charsCode`, `strCode`, `termCode`, `termsCode`, `formCode`, sus inyectividades e `IsFormula`); la demostrabilidad es `Prf` (`Meta/Hilbert.lean`) y su aritmetización, `provCodeC'` (`Meta/ProofChain.lean`).»

**1a‑28** · `Provability.lean:228‑230` · NOTA (A). Texto: «(✏️ 2026‑10‑14, ADR‑134: y Gödel I / > va hoy entero y sin hipótesis: `godelCN_indecidible` —`goedel_I` y `goedel_I_neg`—, en / > `Meta/SolidezVerificador.lean`.)»

**1a‑29 + 1a‑30 (:407/:411)** · `HilbertSeq.lean:412‑415` · NOTA (A).
- Evidencia: `git log -S "def demFormula"` sale vacío, así que nunca fue una declaración. La fórmula Σ₁ de la Fase 2 fue `provFormulaC` (`CheckArith.lean:66`, sobre `validProofFn`), y la de la cadena es `provFormulaC'` (`ProofChain.lean:107`). F7a es f03eacf (2026‑07‑09). He afinado la sugerencia del verificador, que sólo nombraba `provFormulaC'`.
- Texto: «(✏️ 2026‑10‑14, ADR‑134: el `Dem` postulado y `dem_iff_provable`, lo que esto «reemplaza», se retiraron en F7a (2026‑07‑09); y `demFormula` nunca existió con ese nombre: la fórmula Σ₁ de la Fase 2 se construyó como `provFormulaC` (sobre `validProofFn`, `Meta/CheckArith.lean`), y la que usa la cadena es `provFormulaC'` (`Meta/ProofChain.lean`).)»

**1a‑30 (:449, :458)** · nombre retirado, mismas evidencias.
- `HilbertSeq.lean:453`: «…de `Meta/Provability.lean` (retirado en F7a, 2026‑07‑09).»
- `HilbertSeq.lean:463`: «(restringido a `⊢ᴴ`; el postulado, retirado en F7a, 2026‑07‑09).»

**1a‑31** · `HilbertDeduction.lean:27‑28` · NOTA (A): la frase es del 2026‑06‑23 y `PrfH.listInd` entró el 2026‑06‑24. Texto: «más `hyp`; ✏️ 2026‑10‑14, ADR‑134: y `listInd`, desde el 2026‑06‑24)».

**1a‑32** · `HilbertDeduction.lean:96‑98` · CORREGIDO (B): nadie lo usó nunca; `git log -S PrfH_w1` sólo da el commit que lo creó.
- Evidencia: grep en el árbol, `sondeos/` y `../FOL`. Fuera de su `export`, sólo aparece en una nota de comentario de `EvalLiftfcPrf.lean:756`. `sondeos/PrfHMono.lean` y `Probe/` (ignorado por git) definen su propia copia.
- Texto: «— el caso que necesitaban los cuatro módulos de arriba; ninguno lo consume (✏️ 2026‑10‑14: decía «el caso que consumen los cuatro módulos»; grep del 2026‑10‑14 en el árbol, `sondeos/` y FOL: fuera de aquí sólo lo nombran comentarios, y `sondeos/PrfHMono.lean` tiene su propia copia).»
- Los punteros de `:61‑63` (`LiftcCodePrf:1426` y los otros tres) siguen siendo correctos.

**1a‑33** · `HilbertDeduction.lean:171` · OMITIDO: el banner de la línea 11 ya nombra `provCodeC'_elim` como retirado. Fue un teorema sobre `⊢` (lo creó 447c49c y lo borró b1dedd1).

**1a‑34** · `DerivCondPrf.lean:26` · CORREGIDO (nombre retirado; el fichero se borró en b1dedd1). Texto: «Porte de `Meta/DerivCond.lean` (D2 ω-level, sobre `⊢`; retirado, ADR‑115) al cálculo finitario `Prf`.»

## NUEVA
- `Axioms.lean:1694‑1695`, la gemela de 1a‑12: «(sorry; retirado, ADR‑115)» es inexacto, por la misma evidencia que 1a‑12. Añadí: «-- ✏️ 2026‑10‑14: desde el 2026‑06‑03 estaba en Block4_C6_C7, y al retirarse no tenía `sorry`)».
- Fuera de mi lista, sin tocar:
  - `Meta/CheckArith.lean:30` repite los dos errores: `demFormula` y «`numeralM 0..17`».
  - `LiftcCodePrf:1426`, `HasWitFTrackedPrf:183` y `HasWitTrackedPrf:757` siguen diciendo en presente que falta `PrfH_mono` (deuda B6b), que está saldada desde el 2026‑09‑11. Para `EvalLiftfcPrf:749` otro agente ya añadió la nota de la l. 756.

## Ficheros tocados y comprobación
`git diff --stat` (árbol contra índice):

| Fichero | `git diff --stat` | Sólo lo mío |
|---|---|---|
| `ROBINSON_PlusPlus.lean` | 6 | +5 −1 |
| `Full/Induction.lean` | 17 | +12 −5 |
| `Meta.lean` | 10 | +8 −2 |
| `Meta/Consistencia.lean` | 4 | +3 −1 |
| `Meta/DerivCondPrf.lean` | 2 | +1 −1 |
| `Meta/DiagonalNumeral.lean` | 4 | +3 −1 |
| `Meta/DiagonalTwo.lean` | 9 | +7 −2 |
| `Meta/GodelTwo.lean` | 4 | +3 −1 |
| `Meta/GodelTwoPrf.lean` | 4 | +3 −1 |
| `Meta/HilbertDeduction.lean` | 7 | +5 −2 |
| `Meta/HilbertSeq.lean` | 14 | +7 −3 |
| `Meta/Provability.lean` | 8 | +7 −1 |
| `Minimal/Axioms.lean` | 39 | +22 −8 |

En `Axioms.lean` y `HilbertSeq.lean`, el stat incluye cambios sin preparar que ya estaban antes de empezar y no son míos (`Axioms.lean` l. 31‑32, 819 y 1585‑1586; `HilbertSeq.lean` l. 42 y 160).

- **Delimitadores:** `/-` y `-/` coinciden antes y después en los 13 ficheros: 1/1, 1/1, 18/18, 104/104, 8/8, 6/6, 12/12, 7/7, 9/9, 13/13, 31/31, 18/18 y 5/5. Las 11 líneas cambiadas que contienen un delimitador conservan el original, desplazado al final del texto ampliado.
- **Finales de línea:** los once ficheros CRLF siguen con CR = LF en todas las líneas; `Consistencia.lean` y `DerivCondPrf.lean` siguen siendo LF puros (0 CR).

Todo está en `<tmp>/scratchpad/suelo/comentarios/`:
- `g1a_mi_diff.patch` — mi diff exacto
- `g1a_antes/` — la copia previa de los 13 ficheros
- `g1a_conteo_antes.txt` — el conteo inicial de delimitadores

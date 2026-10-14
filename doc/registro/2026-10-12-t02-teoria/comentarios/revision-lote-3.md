# Revisión adversarial del lote de comentarios · parte 3

**Last updated:** 2026-10-14 — registro (ADR‑134): copia tal cual de lo que se produjo ese día; no se actualiza. La marca está para el control `[E]` de `check-doc-sync.bash`, que mira todo `.md` versionado.

> Registro: el informe final de un agente de sólo lectura, tal cual (fecha: 2026-10-14). Lo que dice del árbol es de esa fecha; lo aplicado, en ADR-134.

Encontré un defecto grave (A), dos inexactos (M) y cinco menores (m). El resto de las afirmaciones nuevas se sostiene.

**Defectos**

1. **`doc/REFERENCE-Incompleteness.md:275‑276`** · gravedad **A**, más M por la cifra
   - Frase: «El footprint de hoy, `[propext, Classical.choice, Quot.sound]` (`prf_inAxC` se retiró).»
   - Es falsa: `prf_inAxC` no se retiró. Hoy es un teorema, `theorem prf_inAxC` en `Meta/Representability2Prf.lean:233`. Pasó de axioma a teorema el 2026‑07‑20 (commit `25d255b`), y por eso dejó de salir en el footprint.
   - El footprint «de hoy» no está medido: `check-footprints.bash` no tiene fila de `d3_prf_of_sigma1` y no hay ningún `#print axioms` de él. Sólo se puede deducir una cota superior, porque el build no declara ningún `axiom` de Lean (ADR‑115; `git grep` no encuentra ninguno).
   - Reemplazo: «El footprint de hoy no se midió: sin `axiom` de Lean en el build (ADR‑115), no puede pasar de `[propext, Classical.choice, Quot.sound]`. `prf_inAxC` no se retiró: es teorema desde el 2026‑07‑20 (`Meta/Representability2Prf.lean`).»

2. **`sondeos/README.md:114`**, fila `InduccionTitulares.lean` · gravedad **M**
   - Frase: «hechos que la lista prueba sin inducción y aquí se probaron con ella».
   - Se presenta como hecho medido, pero su fuente, `AXIOMS.md` §0.3, sólo dice «por lectura los CUATRO usos de D1 son evitables… Que D1 compile sin `ind` no está comprobado». Para `prf_zero_or_succ` y `prf_mul_le_mono_right` la derivación sin inducción no está escrita en ningún sitio.
   - Reemplazo: «hechos que, por lectura, la lista prueba sin inducción (`AXIOMS.md` §0.3; sin compilar) y aquí se probaron con ella».

3. **`sondeos/MedirF_Censo.lean:85`** · gravedad **m**
   - Frase: «`Meta/AxiomListCode.lean`, con `neg_In_axiomsCodeT` y su consumidor, se retiró con la capa `⊢`».
   - Da a entender que el consumidor vivía en ese fichero, y no es así. `derives_lineWF_neg_thy_of_not_prf` estaba en `Meta/LineWFCases.lean:244` (`git grep … b1dedd1^`), que sigue existiendo; salió de él en el mismo commit `b1dedd1`.
   - Reemplazo: «`Meta/AxiomListCode.lean`, con `neg_In_axiomsCodeT`, se retiró con la capa `⊢` (ADR‑115), y su consumidor `derives_lineWF_neg_thy_of_not_prf` salió de `Meta/LineWFCases.lean` en el mismo commit».

4. **`doc/REFERENCE-Incompleteness.md:653‑655`** · gravedad **m**
   - La nota nueva («⛔ VACUO, como `d3_prf_of_sigma1`…») deja sin tocar la línea de encima, `-- #print axioms = [propext, Classical.choice, Quot.sound, prf_inAxC]`, que está caducada por la misma razón que el defecto 1.
   - Reemplazo: añadir a la nota «Footprint sin re‑medir; `prf_inAxC` es teorema desde el 2026‑07‑20».

5. **`sondeos/README.md:3`** y **`:93`** · gravedad **m**
   - La marca `**Last updated:** 2026-10-13` sigue igual aunque el fichero se editó el 2026‑10‑14. `sondeos/README.md` no está en la tabla de deuda `E_DEUDA` de `check-doc-sync.bash`, así que el control `[E]` romperá si no se pone la fecha del commit.
   - El párrafo `✏️ *(2026‑10‑12, ADR‑134)*` contiene ahora frases escritas el 2026‑10‑14 (el título de `ModeloBasura`, lo de `ModeloNat`) bajo la fecha del 12.
   - Reemplazo: «**Last updated:** <fecha del commit> — …» y «✏️ *(2026‑10‑12; ampliado el 2026‑10‑14, ADR‑134)*».

6. **`doc/REFERENCE-Incompleteness.md:796`** · gravedad **m**
   - Frase: «(✏️ ADR‑134: `d3_prf_real` pasa por ella, vía `d3_prf_of_chainOkDot`)».
   - Lo que afirma es cierto: la cadena es `d3_prf_real` → `d3_prf_of_halves` → `d3_prf_of_hbody` → `d3_prf_of_chainOkBDot` → `d3_prf_of_chainOkDot` → `d3_prf_of_dotted_atoms`, comprobada en el fuente.
   - Pero es la única nota del lote sin fecha. Además da por buena una firma que ya estaba mal: el `hI` real lleva la guarda `chainOk nil (.var 0) ⇒` delante (`Meta/D3DottedPrf.lean:139`).
   - Reemplazo: «(✏️ 2026‑10‑14, ADR‑134: `d3_prf_real` pasa por ella, vía `d3_prf_of_chainOkDot`; el `hI` real lleva delante `chainOk nil #0 ⇒`)».

7. **`doc/REFERENCE-Incompleteness.md:125`** · gravedad **m**
   - Frase: «decía «incl + p3 + mp + gen»».
   - La cita no es literal: el texto decía «clásico: incl (Prfᵢ) + p3 (DNE) + mp + gen».
   - Reemplazo: «decía «incl (Prfᵢ) + p3 (DNE) + mp + gen»».

**Sintaxis de los `.lean`:** está bien. Ningún fichero cambia su número de `/-` ni de `-/` (sólo `MedirF_Censo` y `PilotoRastreada` los mueven de línea, uno por uno). Los acentos graves quedan en número par en todos, ninguna línea nueva escribe `prf_axiomsCodeT_eq` y no hay finales de línea mezclados.

**Lo que se sostiene, por si quieres saberlo:**
- Todos los «hoy no compila» casan con `tabla_adr129.txt` (rc 1), y `Magnitud` tiene rc 0. Las causas que se citan coinciden con el primer error de la tabla: el `= 2` en `CanonNeRefuta:56` y `PilotoRastreada:30`, `AxiomListCode` en `MedirF_*`, `FOL.MetaRules.raa` en `HenkinSaleDeRaa`.
- `consN 0 0 = triN 0 + 0 + 1 = 1`, con `nil := zero` y `numeralM 0 = zero`.
- «Tres de 142»: lo mide `filtro_occ'`.
- 48 de 226, 158 de 182 y las 182 filas con `choice` de hoy: casan con ADR‑122, ADR‑131 y `check-footprints.bash`.
- Las dos notas VACUO casan con `sondeos/D3Sigma1Vacuo.lean`: `hbI_refutable` se obtiene de `hI_refutable` vía `prf_hI_of_reflect_boundedIn`, y `L` es `cons zero nil`.
- Las fechas de FOL: `Completeness.lean` se borró el 2026‑09‑23 (`62dc2d5`, «superado por `Canonical0.completeness₀`») y `MetaRules.lean` el 2026‑10‑02 (`3b355d7`).
- Los retiros de ADR‑115 (`codeNat_ne`, `numeral_ne`, `charsCode_ne`, `strCode_ne`, `NegVerifier`) están confirmados con `git log -S`.
- Existen todos los nombres citados: `control_tc_cons` (vale para todo `V`), `PrfH_mono`/`PrfH_w1`, `pcc_tc_objAt` con el orden que dice la nota, `prf_div2_numeral`, `prf_cons_div2`, `instFreshSymListChar` y `FOL/Derives0.lean`.

Comprobé unas 130 afirmaciones nuevas: se sostienen unas 122; las 8 que fallan son el defecto 1 (que cuenta dos) y los defectos 2 a 7.

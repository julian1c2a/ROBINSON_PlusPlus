# Corrección de comentarios · grupo 5 (cabeceras de los sondeos)

**Last updated:** 2026-10-14 — registro (ADR‑134): copia tal cual de lo que se produjo ese día; no se actualiza. La marca está para el control `[E]` de `check-doc-sync.bash`, que mira todo `.md` versionado.

> Registro: el informe final de un agente de sólo lectura, tal cual (fecha: 2026-10-14). Lo que dice del árbol es de esa fecha; lo aplicado, en ADR-134.

He corregido los comentarios de los 39 sondeos de mi lista y la nota de `sondeos/README.md`. Los 31 hallazgos se sostienen contra el fuente: ninguno RECHAZADO ni OMITIDO, y hay 3 NUEVOS. Sólo he tocado comentarios: los `/-` y `-/` cuadran en todos los ficheros, los finales de línea y el UTF‑8 se conservan, y no he ejecutado `lake`, `lean` ni ningún git de escritura.

La nota repetida de 5‑30 dice: «(✏️ 2026‑10‑14, ADR‑134: ese axioma ya no existe; desde ADR‑117 el ancla es el axioma diagonal `ax_axiomsCodeT_def` y `prf_ancla` es teorema.)»

La nota repetida de 5‑31 dice: «(✏️ 2026‑10‑14, ADR‑134: hoy no compila —`sondeos/pasadas/tabla_adr129.txt`, 2026‑10‑05—; es registro.)»

Los demás textos exactos se ven con `git diff -- sondeos/`. Todas las rutas son de `sondeos/`, con la línea ya editada.

## Hallazgos

| id | fichero:línea | acción | evidencia y texto nuevo |
|---|---|---|---|
| 5‑01 | `AnclaEqInconsistente.lean:12‑13` y `:18‑20` | NOTA (amplía la ✏️ de ADR‑117) | Ni `class AnclaEq` ni `instAnclaEq` aparecen en ningún `.lean`. `prf_ancla` está en `Meta/Representability2Prf.lean:157`; `consistencia` en `Meta/Consistencia.lean:50`; `MN_axioms` en `Meta/ModeloCodificacion.lean:343`. Texto: «…instancia `instAnclaEq`; ✏️ 2026‑10‑14, ADR‑134: ADR‑118 retiró la clase y su instancia, y queda el teorema `prf_ancla`)…» y «(✏️ 2026‑10‑14, ADR‑134: desde ADR‑120 lo hay —`MNV V₀` satisface los 142, `MN_axioms`— y `consistencia : ConsistentH` (`Meta/Consistencia.lean`) prueba la consistencia de `Prf`, los 142 CON los esquemas; este sondeo no usa el modelo y sigue sin probarla.)» |
| 5‑02 | `AnclaEqInconsistente.lean:76‑78` | NOTA | Es ADR‑133 (M‑11). `ax_axiomsCodeT_eq` está retirado (DECISIONS.md:27). No repito su nombre. Texto: «ese axioma se retiró con la capa `⊢`, ADR‑115. Y la razón es M‑11 al revés, corregida en ADR‑133: inducir sobre un inductivo habitado por `axiom`s es válido; lo que puede ser falso es el `axiom`, si contradice lo que se demuestra por inducción.» |
| 5‑03 | `AnclaSoundness.lean:27‑29` | NOTA (párrafo ✏️ nuevo en el bloque del 2026‑10‑04) | Desde ADR‑119/120 el modelo existe (`MNV V₀`, `MN_axioms`) y `ConsistentH` es teorema (`consistencia`, por `prf_sound`). La sección «⬜ Lo que sigue faltando» y el ⬜ de `ancla_underivable_prfI` quedan como registro. |
| 5‑04 | `AnclaSoundness.lean:89‑91` | NOTA | `axD` (`Minimal/Axioms.lean:1111`) pone `axiomsCodeT =eq …` fuera de `In`. `filtro_occ'` da tres axiomas. Texto: «desde ADR‑117 son tres de los 142: el ancla `ax_axiomsCodeT_def` lo nombra FUERA de `In`, como lado izquierdo de una ecuación…» |
| 5‑05 | `AnclaSoundness.lean:67‑69` | NOTA | Es la M‑11 vieja. `prf_sound` (`Meta/SolidezPrf.lean:145`) es `induction h`. |
| 5‑06 | `ModeloDiscriminador.lean:9‑10` | NOTA | El texto propuesto por el grupo, citando `MN_axioms`. |
| 5‑07 | `PrfBotCodificacionVieja.lean:35‑36` | NOTA | El texto propuesto: la probó el modelo de los 142, `consistencia`, ADR‑120. |
| 5‑08 | `OmegaConsistentRefutable.lean:46‑47` | NOTA | `goedel_I_neg` está en `Meta/SolidezVerificador.lean:558`. |
| 5‑09 | `CantorSobreyectivo.lean:13‑16` | NOTA | `ax_L0_cons_def` (`Minimal/Axioms.lean:367`) es hoy `σ (pair …)`; `consN` en `:642`. |
| 5‑10 | `CanonNeRefuta.lean:22‑25` y `:40‑41` | NOTA ×2 | La cuenta pasa a ser con el 1 (`cons_cero_cero_en_Prf`) y el sondeo no compila (tabla: rc 1). `codeNat_inj` está en `Meta/CodeNatInjPrf.lean:150`; `codeNat_ne` era sobre `⊢` y se retiró. |
| 5‑11 | `ClassicalChoiceCenso.lean:70‑71`, `:75‑78`, `:94‑95` | NOTA ×3 | La raíz `String` ya no existe: `strCode`/`strCodeM` son `List Char` (`Meta/Provability.lean:39`, `Minimal/Axioms.lean:599`). «La mayor parte es esto», refutado en los titulares: 48 de 226 (ADR‑122) y 158 de 182 (ADR‑131); sobre las 3 143 declaraciones no se re‑midió. El ⬜, hecho por D7; no afirmo nada de las 6 de `Enumeration`. |
| 5‑12 | `CodeNatInj.lean:4‑7` | NOTA de cabecera | La fórmula de `consN` es la vieja y el sondeo no compila (rc 1). La promoción está hecha: `consN_inj`, `codeNat_inj` y `num_bridge` en `Meta/CodeNatInjPrf.lean`. `numeral_ne`, `codeNat_ne` y `NegVerifier` se retiraron con ADR‑115. |
| 5‑13 | `D3Sigma1Vacuo.lean:22‑24` | CORREGIDO (B) | `Meta/Sigma1BoundedPrf.lean:87` usa `d3_prf_of_sigma1`. Texto: «Ninguno tiene consumidor fuera del par (✏️ 2026‑10‑14: decía «Ninguno tiene consumidor»; `d3_prf_of_reflect_bounded` consume a `d3_prf_of_sigma1`, `Meta/Sigma1BoundedPrf.lean`)». |
| 5‑14 | `DerivesSinMetaReglas.lean:19‑20` y `:47‑48` | NOTA ×2 | Es la M‑11 vieja. `FOL/MetaRules.lean` ya no existe (FOL `3b355d7`). `Derives₀` existe: `../FOL/FOL/Derives0.lean:126`. |
| 5‑15 | `HenkinSaleDeRaa.lean:15‑17` | NOTA de cabecera | ADR‑032 decidió la opción (A). `cuarentena/Completeness.lean` se borró el 2026‑09‑23 (FOL `62dc2d5`); la supera `completeness₀` (`FOL/Canonical0.lean:658`). `MetaRules` se borró el 2026‑10‑02. |
| 5‑16 | `KitPayoff.lean:38‑39` | NOTA | `pcc_tc_objAt` está en `Meta/CodeTreeReflect.lean:225`, con la igualdad en el otro orden. `prf_tc_objAt` no está declarado en ningún sitio. |
| 5‑17 | `Magnitud.lean:8‑10` | NOTA | `L` usa `σt` y el sondeo compila (rc 0): lo que imprime son las magnitudes de la codificación anterior. |
| 5‑18 | `MDiezEnLaFirma.lean:10‑12` | NOTA (`--`) | ADR‑024 («`raa` e `imp_intro`»), ADR‑115 y ADR‑133 (M‑10). |
| 5‑19 | `MedirC_Enmienda.lean:33‑35` | NOTA | Hoy son 142 y `ax_lineWF_q1` está en `codingAxioms` (`Minimal/Axioms.lean:1645`). La dependencia de `godelCN` no se re‑midió. |
| 5‑20 | `MedirF_Censo.lean:85‑86`, `MedirF_Opaco.lean:11‑12`, `MedirF_Replan.lean:34‑37` | NOTA ×3 | `Meta/AxiomListCode.lean` se borró en `b1dedd1` (ADR‑115). La tabla da para los tres «unknown namespace AxiomListCode». |
| 5‑21 | `ModeloBasura.lean:8‑10` | NOTA | ADR‑113, `MN_axioms`, `prf_sound`; el sondeo mide con `consOldN` (`:81`). |
| 5‑22 | `ModeloNat.lean:56‑57` y `:63‑64` | NOTA ×2 | `control_tc_cons` está en `Meta/ModeloCodificacion.lean:391`, con `variable {V}`, así que vale para todo `V`. El caso «Rosser» (D): ahora apunta a `goedel_I_neg`. |
| 5‑23 | `NegVerifierModE.lean:27‑29`, `:34‑36`, `:48‑49` | NOTA ×3 | Hoy `numeralM 1`. ADR‑022, ADR‑114 y ADR‑115. El sondeo no compila (rc 1). |
| 5‑24 | `NombresFrescosMedicion.lean:36‑37` | NOTA | ADR‑129: `instFreshSymListChar` no depende de ningún axioma. |
| 5‑25 | `PilotoRastreada.lean:14‑17` y `:34` | NOTA ×2 | La nota «`prf_tc_cons'` RETIRADO» de `Meta/EvalListPrf.lean:79`; `pcc_dot_cons` en `Meta/DotConsPrf.lean:335`. Error de la tabla en `:30` (`consN 0 0 = 2 := rfl`). |
| 5‑26 | `PrfHMono.lean:52` | NOTA | `Meta/HilbertDeduction.lean:77` y `:99`. |
| 5‑27 | `RecodCoste.lean:29‑31` y `:54‑56` | NOTA ×2 | `charsCode_ne` y `strCode_ne` se retiraron en `b1dedd1`; los otros 9 nombres de la lista existen. El ancla es diagonal y lleva `nD axiomsBase`. |
| 5‑28 | `S1Audit.lean:5‑8` y `S4.lean:8‑10` | NOTA ×2 | El build no declara ningún `axiom`; `ax_tc_cons` está en `Minimal/Axioms.lean:925` y lo refuta `control_tc_cons`. `prf_div2_numeral` está en `Meta/Div2ParityPrf.lean:262`; `prf_cons_div2` en `Meta/CantorMonoPrf.lean:257`. |
| 5‑29 | `SimbolosSinString.lean:46‑48` | NOTA | Refutado tras D7: siguen 182 filas con `Classical.choice`, y en 158 entra sólo por dos cancelaciones de lift (ADR‑131). |
| 5‑30 | `DiscriminaEcuacional`, `DiscriminaTestigoAbierto`, `ParticionDiscrimina`, `ParticionTresPredicados` `:30`; `InTracked:13`; `KitPayoff:20`; `ReflectorForallAnidado:41`; `A3IsFCBTracked:10` | NOTA ×8 | El texto repetido de arriba. |
| 5‑31 | `MedirC_Carga:12`, `MedirC_Enmienda:6`, `MedirF_Opaco:11`, `NegVerifierModE:48`, `ClausuraNoHaceFalta:11`, `CanonNeRefuta:25`, `ReflectorForallAnidado:31`, `InTracked:69`, `ParseWitness:59`, `HenkinSaleDeRaa:87‑88` | NOTA ×10 | Los diez tienen rc 1 en `tabla_adr129.txt`. |
| 5‑40 | `README.md:97‑99` y la fila de `ModeloNat` (`:117`) | NOTA | Amplía la nota ADR‑134: «Lo mismo el título de `ModeloBasura` («ℕ NO ES MODELO DE `Prf`», con la codificación de antes de ADR‑113) y, en `ModeloNat`, «`⊬¬G` (Rosser)» y el control negativo «pendiente» (también en su fila), hecho en el build (`control_tc_cons`, ADR‑124).» En la fila: «(✏️ 2026‑10‑14, ADR‑134: las dos, hechas: la promoción, ADR‑120; el control, `control_tc_cons` en `Meta/ModeloCodificacion.lean`, ADR‑124)». No toqué `Last updated` ni nada más. |

## NUEVAS

- **`AnclaEqInconsistente.lean:644`**: el bloque de registro decía «desde ADR‑117 el ancla es una instancia». Nota: «desde ADR‑118 ni la clase `AnclaEq` ni su instancia existen».
- **`ModeloDiscriminador.lean:38`**: la «lista blanca» es de la M‑11 vieja. Nota que remite a ADR‑133 y a `prf_sound`.
- **`SimbolosSinString.lean:58`**: decía que «cambia `G`». Nota: según ADR‑129, ningún valor cambió.

## Para el coordinador (fuera de mi lista, sin tocar)

- **README `:112`**: la fila de `D3Sigma1Vacuo` dice «Ninguno de los dos teoremas tiene consumidor», lo mismo que 5‑13.
- **`Meta/CodeNatInjPrf.lean:25` y `:33`**: siguen con «`cons nil nil = 2`» y la fórmula vieja de `consN`.
- **`ClassicalChoiceCenso.lean:26`**: la frase de `value?` la discute `AUDITORIA-SUELO` (:780). No la he medido ni editada.
- **Punteros desplazados por las líneas nuevas**: `S1Audit.lean:22` pasa a `:26` (citado en `doc/AUDITORIA-SUELO-2026-10-12.md:812`) y `A3IsFCBTracked.lean:205` pasa a `:208` (citado en `doc/REFERENCE-Incompleteness.md:3390`).

## Ficheros tocados (`git diff --stat`)

A3IsFCBTracked 3 · AnclaEqInconsistente 12 · AnclaSoundness 11 · CanonNeRefuta 7 · CantorSobreyectivo 5 · ClassicalChoiceCenso 11 · ClausuraNoHaceFalta 1 · CodeNatInj 5 · D3Sigma1Vacuo 3 · DerivesSinMetaReglas 5 · DiscriminaEcuacional 2 · DiscriminaTestigoAbierto 2 · HenkinSaleDeRaa 7 · InTracked 4 · KitPayoff 5 · MDiezEnLaFirma 3 · Magnitud 3 · MedirC_Carga 1 · MedirC_Enmienda 4 · MedirF_Censo 4 · MedirF_Opaco 2 · MedirF_Replan 4 · ModeloBasura 4 · ModeloDiscriminador 5 · ModeloNat 6 · NegVerifierModE 11 · NombresFrescosMedicion 2 · OmegaConsistentRefutable 2 · ParseWitness 2 · ParticionDiscrimina 2 · ParticionTresPredicados 2 · PilotoRastreada 8 · PrfBotCodificacionVieja 3 · PrfHMono 1 · RecodCoste 8 · ReflectorForallAnidado 3 · S1Audit 4 · S4 3 · SimbolosSinString 6 · README.md 17 (incluye los cambios previos del coordinador; los míos son 3 líneas de la nota y 1 de la fila).

## Comprobación de `/-` y `-/` (antes = después)

AnclaEqInconsistente 46/46 · AnclaSoundness 11/11 · ModeloDiscriminador 10/10 · PrfBotCodificacionVieja 6/6 · OmegaConsistentRefutable 5/5 · CantorSobreyectivo 6/6 · CanonNeRefuta 5/5 · ClassicalChoiceCenso 2/2 · CodeNatInj 9/9 · D3Sigma1Vacuo 2/2 · DerivesSinMetaReglas 2/2 · HenkinSaleDeRaa 6/6 · KitPayoff 7/7 · Magnitud 5/5 · MDiezEnLaFirma 7/7 · MedirC_Enmienda 59/59 · MedirF_Censo 46/46 · MedirF_Opaco 28/28 · MedirF_Replan 31/31 · ModeloBasura 5/5 · ModeloNat 62/62 · NegVerifierModE 14/14 · NombresFrescosMedicion 2/2 · PilotoRastreada 8/8 · PrfHMono 5/5 · RecodCoste 3/3 · S1Audit 6/6 · S4 2/2 · SimbolosSinString 3/3 · DiscriminaEcuacional 127/127 · DiscriminaTestigoAbierto 112/112 · ParticionDiscrimina 98/98 · ParticionTresPredicados 78/78 · InTracked 8/8 · ReflectorForallAnidado 38/38 · A3IsFCBTracked 38/38 · MedirC_Carga 42/42 · ClausuraNoHaceFalta 41/41 · ParseWitness 19/19 · README 0/0.

En los 17 ficheros CRLF, el número de CR sigue igual al de líneas; los LF siguen sin ningún CR. En las líneas añadidas no hay fechas ni «ADR‑» con guion ASCII, ni `prf_axiomsCodeT_eq`, y los acentos graves están emparejados en cada línea. Las cuentas de antes están en `scratchpad/suelo/comentarios/g5/antes.txt`.

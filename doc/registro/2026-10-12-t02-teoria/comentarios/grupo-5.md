# Grupo 5 · las cabeceras de los sondeos

**Last updated:** 2026-10-14 — registro (ADR‑134): copia tal cual de lo que se produjo ese día; no se actualiza. La marca está para el control `[E]` de `check-doc-sync.bash`, que mira todo `.md` versionado.

Ficheros: los `sondeos/*.lean` nombrados abajo (y ningún otro; NUNCA `sondeos/InduccionTitulares.lean`), y en
`sondeos/README.md` SÓLO la nota «✏️ … ADR‑134» que ya existe y la fila de ModeloNat/ModeloBasura (ver 5‑40).

Los sondeos son REGISTRO: experimentos fechados. Su cabecera puede contar lo que se midió aquel día, pero no debe
afirmar en PRESENTE algo que hoy es falso sin una marca. Forma: una nota al principio de la cabecera o junto a la
frase, `(✏️ 2026‑10‑14, ADR‑134: <lo de hoy>)`. No cambies el código de ningún sondeo (ni siquiera para que compile).
Cuáles compilan hoy: `sondeos/pasadas/tabla_adr129.txt` (`fichero|rc|segundos|error`; rc 0 = compila; medido el
2026‑10‑05, ADR‑129). Si un sondeo NO está en esa tabla, no afirmes nada sobre si compila.

Prioridad: A = falso hoy y relevante; M = media; D = dudoso; m = menor.

## Los que el censo ya encontró (siguen sin marca en su propio fichero)
- 5‑01 · `AnclaEqInconsistente.lean:12` y `:16‑17` · la nota ✏️ dice «instancia `instAnclaEq`», que ADR‑118 retiró;
  y que no prueba que los 142 sean consistentes. → «…`AnclaEq` es TEOREMA (`prf_ancla`; ADR‑118 retiró la clase y su
  instancia)… (✏️ ADR‑120: la consistencia la prueba `consistencia`.)» **A**
- 5‑02 · `AnclaEqInconsistente.lean:72‑73` · cita el viejo axioma del ancla (no escribas su nombre) y dice que la
  inducción sobre `Derives` no vale (M‑11 al revés; ADR‑133 la corrigió: inducir sobre un inductivo habitado ES
  válido; lo falso era postular un `axiom` que contradice lo inducible). **M**
- 5‑03 · `AnclaSoundness.lean:77‑83` · añadir a la ✏️ del 04‑10: «✏️ ADR‑119/120: el modelo existe (`MNV V₀`,
  `MN_axioms`, los 142) y `ConsistentH` es teorema; la sección ⬜ es registro.» **A**
- 5‑04 · `AnclaSoundness.lean:81‑82` · «dos de los 141, dentro de `In`» · hoy son tres de 142 y el ancla lo nombra fuera
  de `In` (compruébalo en `Minimal/Axioms.lean`, `ax_axiomsCodeT_def`). **A**
- 5‑05 · `AnclaSoundness.lean:61‑64` · M‑11 a la manera vieja, que la ✏️ ADR‑133 no cubre. **M**
- 5‑06 · `ModeloDiscriminador.lean:5‑8` · → «(✏️ 2026‑10‑14, ADR‑134: `ConsistentH` es teorema desde ADR‑120,
  `consistencia`; modelo de los 142.)» **A**
- 5‑07 · `PrfBotCodificacionVieja.lean:34‑35` · → «(✏️ 2026‑10‑14, ADR‑134: la consistencia la probó el modelo de los
  142, `consistencia`, ADR‑120.)» **A**
- 5‑08 · `OmegaConsistentRefutable.lean:44‑45` · → «(✏️ 2026‑10‑14, ADR‑134: `⊬¬G` salió sin ω‑consistencia ni
  Rosser: `goedel_I_neg`, ADR‑121.)» **A**
- 5‑09 · `CantorSobreyectivo.lean:9‑12` · la frase sobre `listInd` es cierta, pero :10 dice en presente que
  `ax_L0_cons_def` es «`cons a b = pair a (σb)`». ADR‑113 adoptó la propuesta de este mismo sondeo
  (`cons a b = σ (pair a b)`) y no hay ✏️. **A**

## Omisiones (cabeceras que han envejecido)
- 5‑10 · `CanonNeRefuta.lean:18‑21` · «cons nil nil = … = 2»; hoy es 1 (compruébalo con `consN`, `Minimal/Axioms.lean`:
  `consN 0 0 = triN 0 + 0 + 1`). **A** · `:35‑36` «Sin medir»; `codeNat_inj` está probada (compruébalo). **A**
- 5‑11 · `ClassicalChoiceCenso.lean:65‑68` · raíz `String`, quitada en D7 (ADR‑129). **A** · `:71‑72` refutado por
  ADR‑122/131 (léelas). **M** · `:84‑88` el ⬜ ya está hecho. **A**
- 5‑12 · `CodeNatInj.lean:37‑45` · (el verificador no detalla: léelo y contrástalo con ADR‑113 y con
  `Meta/CodeNatInjPrf.lean`). **A**
- 5‑13 · `D3Sigma1Vacuo.lean:22‑23` · «Ninguno tiene consumidor» · `d3_prf_of_reflect_bounded` consume a
  `d3_prf_of_sigma1` (compruébalo en `Meta/Sigma1BoundedPrf.lean`); ninguno tiene consumidor FUERA de ese par. **M**
- 5‑14 · `DerivesSinMetaReglas.lean:16‑18` y `:43‑45` · `Derives₀` «sería nuevo»; ya existe (FOL). **A**
- 5‑15 · `HenkinSaleDeRaa.lean:29‑34` y `:72‑83` · `raa` y `Completeness` borrados (ADR‑115); no compila desde el
  2026‑10‑02 (compruébalo en la tabla). **A**
- 5‑16 · `KitPayoff.lean:27‑36` · `prf_tc_objAt`; hecho como `pcc_tc_objAt` (`Meta/CodeTreeReflect.lean`). **A**
- 5‑17 · `Magnitud.lean:4‑6` · calcula con el `cons` viejo y compila, así que imprime magnitudes viejas sin avisar
  (compruébalo). **A**
- 5‑18 · `MDiezEnLaFirma.lean:6‑9` · «axioms ⊢ es COMPLETO», en presente (⊢ retirado, ADR‑115). **A**
- 5‑19 · `MedirC_Enmienda.lean:29‑31` · (léelo). **M**
- 5‑20 · `MedirF_Censo.lean:82‑84`, `MedirF_Opaco.lean:10` y `:17‑26`, `MedirF_Replan.lean:30‑34` · «AxiomListCode en
  producción», «Todo COMPILA» (compruébalo con grep en el build y en la tabla). **A**
- 5‑21 · `ModeloBasura.lean:4` · título «ℕ NO ES MODELO DE `Prf`» (ADR‑088, con el `cons` viejo; ADR‑113 lo
  resolvió y ADR‑119/120 dieron el modelo). **M**
- 5‑22 · `ModeloNat.lean:55‑56` · control negativo «pendiente»; está hecho: `control_tc_cons`, ADR‑124. **A** ·
  `:62` «(Rosser)». **D**
- 5‑23 · `NegVerifierModE.lean:24‑25` · «≐ numeralM 2»; hoy 1. **A** · `:29‑44`. **M**
- 5‑24 · `NombresFrescosMedicion.lean:32‑35` · (léelo). **A**
- 5‑25 · `PilotoRastreada.lean:4‑11` y `:28` · (léelo). **A**
- 5‑26 · `PrfHMono.lean:48‑51` · «No los mueve a producción»; ya están (`PrfH_mono`, `PrfH_w1`,
  `Meta/HilbertDeduction.lean`). **A**
- 5‑27 · `RecodCoste.lean:45‑50` **A**; `:23‑59` **M** · (léelo).
- 5‑28 · `S1Audit.lean:2‑4` **A** · `S4.lean:5‑7` **M** · (léelos).
- 5‑29 · `SimbolosSinString.lean:43‑45` · «a una composición de estar limpia»; refutado tras D7 (ADR‑129, ADR‑131). **A**

## Patrones
- 5‑30 · **El viejo axioma del ancla, «la base sancionada»** · `DiscriminaEcuacional.lean`,
  `DiscriminaTestigoAbierto.lean`, `ParticionDiscrimina.lean` y `ParticionTresPredicados.lean` (≈ :29 en los
  cuatro), `InTracked.lean:12`, `KitPayoff.lean:19`, `ReflectorForallAnidado.lean:39`, `A3IsFCBTracked.lean:7` ·
  nota: «(✏️ 2026‑10‑14, ADR‑134: ese axioma ya no existe; desde ADR‑117 el ancla es el axioma diagonal
  `ax_axiomsCodeT_def` y `prf_ancla` es teorema.)» (No escribas el nombre viejo.) **M**
- 5‑31 · **«compila» en presente y hoy no** (según `tabla_adr129.txt`) · `MedirC_Carga.lean:9`,
  `MedirC_Enmienda.lean:5`, `MedirF_Opaco.lean:10`, `NegVerifierModE.lean:44`, `ClausuraNoHaceFalta.lean:10`,
  `CanonNeRefuta.lean:21`, `ReflectorForallAnidado.lean:30`, `InTracked.lean:65`, `ParseWitness.lean:57` y
  `HenkinSaleDeRaa.lean:83` · nota: «(✏️ 2026‑10‑14, ADR‑134: hoy no compila —`sondeos/pasadas/tabla_adr129.txt`,
  2026‑10‑05—; es registro.)» Compruébalo en la tabla, uno a uno. **M**

## sondeos/README.md
- 5‑40 · la nota ✏️ ADR‑134 de `sondeos/README.md` (búscala: «ADR‑134») enumera sondeos con cabeceras viejas, pero
  no cubre `ModeloBasura.lean:4` ni `ModeloNat.lean:55‑62`, ni la fila de ModeloNat (≈ :114 del README). Amplía la
  nota (o la fila) con lo mínimo. NO toques la línea `**Last updated:**` ni nada más del README.

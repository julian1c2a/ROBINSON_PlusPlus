# Verificación del censo de los .lean

**Last updated:** 2026-10-14 — registro (ADR‑134): copia tal cual de lo que se produjo ese día; no se actualiza. La marca está para el control `[E]` de `check-doc-sync.bash`, que mira todo `.md` versionado.

> Registro: el informe final de un agente de sólo lectura, tal cual (fecha: 2026-10-14). Lo que dice del árbol es de esa fecha; lo aplicado, en ADR-134.

## Resultado: verificación del censo T02 de comentarios `.lean` y búsqueda de omisiones

Todo fue de sólo lectura: no ejecuté lake ni lean, y no toqué el repositorio ni el índice. Las rutas son relativas a `E:/dropbox/github/lean4/ROBINSON_PlusPlus/`; omito el prefijo `ROBINSON_PlusPlus/` en `Meta/`, `Full/` y `Minimal/`.

**Aviso: el árbol cambió mientras revisaba.** Hacia las 14:5x del 14‑10 aparecieron cambios sin indexar, encima de los del índice, en:
- `Meta/CodeNumeralPrf.lean`: nota reescrita.
- `Meta/HilbertSeq.lean`: el título de :160 ya está arreglado.
- `Meta/NatMulPrf.lean`: nota nueva en :96‑97.
- `Minimal/Axioms.lean`: una línea más en la cabecera, así que desde :31 todo va una línea por delante del índice.
- `sondeos/InduccionTitulares.lean` y `sondeos/README.md`.

Las líneas que doy son las del árbol a las 15:10.

**Cómo lo hice.** Lancé 7 barridos en paralelo: 6 sobre las ≈12 700 líneas de comentario de los 114 ficheros del build y 1 sobre las cabeceras de los 92 sondeos. Cada hallazgo se contrastó con el fuente y con un índice de nombres declarados (RPP, sondeos, FOL y el núcleo de Lean 4.31). Yo re‑verifiqué a mano unos 50, entre ellos todos los de prioridad A de las familias C3/D3, consumo y vacuidad. Las herramientas quedaron en `scratchpad/verif_t02/`.

### Conclusiones principales
- **(a)** De los 20 hallazgos FALSO‑VIGENTE, DUDOSO o HISTÓRICO‑SIN‑MARCA, 9 están ARREGLADOS en el índice.
  - Siguen falsas las 6 frases «⊬¬G no tiene formulación sobre `Prf`».
  - Siguen sin marca en su propio fichero las 5 cabeceras de sondeo; sólo las marca la nota de `sondeos/README.md`.
  - El censo no tiene ningún ERROR.
- **(b)** Revisé 31 hallazgos CIERTO o HISTÓRICO‑MARCADO. 25 se sostienen y reclasifico 6.
- **(c)** Hay unas 140 omisiones en el build y unas 40 en cabeceras de sondeos. El censo buscaba cómo se describe la teoría; lo que más se le escapa es el **estado** del proyecto:
  - Unas 40 líneas de 20 módulos dan C3/D3 por pendientes o `pcc_lineWF_tracked` por condicional, cuando están cerrados desde el 2026‑09‑10.
  - 8 bloques `export` dicen «nada lo consume» y no es cierto.
  - 6 módulos presentan como reducción con contenido la ruta `hI`/`hbI`, que ADR‑132 demostró vacua.
  - Unos 15 nombres inexistentes se citan como vigentes.
  - Hay dos errores de contenido matemático: la fórmula de Cantor de `Minimal/Axioms.lean:108` y la de `consN` en `Meta/CodeNatInjPrf.lean:33`.

---

## (a) Estado de los 20 hallazgos

| # | Línea en el árbol | Clase en el censo | Estado | Arreglo o nota |
|---|---|---|---|---|
| 1 | `Meta/NatArithPrf.lean:33‑38` | FALSO‑VIGENTE | ARREGLADO | ✏️ en :36‑38 (queda como HISTÓRICO‑MARCADO). La historia la confirma git: `ax6` está desde `a2124e5` (2026‑05‑09) y el fichero desde `2d7c17c` (2026‑07‑07). |
| 2 | `NatArithPrf:61‑62` | FALSO‑VIGENTE | ARREGLADO | Reescrito en la propia línea. |
| 3 | `NatArithPrf:86‑87` | FALSO‑VIGENTE | ARREGLADO | Reescrito en la propia línea. |
| 4 | `Meta/NatOrderPrf.lean:83‑85` | FALSO‑VIGENTE | ARREGLADO | ✏️ en :85. |
| 5 | `Meta/ChainNegPrf.lean:46` | FALSO‑VIGENTE | SIGUE‑FALSO | «⇒ Hoy `NegVerifier` no existe; la mitad `⊬¬G` está sobre `Prf` desde ADR‑121 por otra vía, sin este módulo: `goedel_I_neg` (`Meta/SolidezVerificador.lean`, la solidez en `MNV V₀`).» |
| 6 | `ChainNegPrf:30‑32` | FALSO‑VIGENTE | SIGUE‑FALSO | «…`⊬¬G` ya está sobre `Prf` sin él (`goedel_I_neg`, ADR‑121): borrarlo o portarlo a Rosser (⬜); hasta entonces es guía de casos.» |
| 7 | `Meta/CodeDistinct.lean:61‑62` | FALSO‑VIGENTE | SIGUE‑FALSO | La misma tesis está en presente en :38‑39 y :51‑60 (ver c). «(✏️ ADR‑121: la mitad `⊬¬G` es hoy `goedel_I_neg`; sale del modelo estándar, no de la ω‑consistencia ni de este módulo.)» |
| 8 | `Meta/DiagonalTwo.lean:93‑95` | FALSO‑VIGENTE | SIGUE‑FALSO | «(✏️ ADR‑121: hoy sí la tiene, `goedel_I_neg`, por la solidez del verificador en `MNV V₀`; Rosser, ⊬R ∧ ⊬¬R sólo con `ConsistentH`, sigue ⬜.)» |
| 9 | `Meta/OmegaReflect.lean:46‑48` | FALSO‑VIGENTE | SIGUE‑FALSO | «La mitad `⊬¬G` está sobre `Prf` desde ADR‑121 (`goedel_I_neg`, sin ω‑consistencia ni Rosser); la ω‑consistencia de antes tampoco vale sobre `Prf`…» |
| 10 | `Meta/VerifierSound.lean:128‑129` | FALSO‑VIGENTE | SIGUE‑FALSO | «…retirados con ADR‑115. (✏️ ADR‑121: la mitad `⊬¬G` es hoy `goedel_I_neg` y no usa este módulo.)» |
| 11 | `Meta.lean:6‑7` | DUDOSO | ARREGLADO | ✏️ sobre T_Prf. La API de :8‑17 sigue sin lo de ADR‑120/121 (ver c). |
| 12 | `Meta/GodelTwoPrf.lean:24‑27` | DUDOSO | ARREGLADO | ✏️ en :26‑27. |
| 13 | `GodelTwoPrf:209‑211` | DUDOSO | ARREGLADO | ✏️ añadida. |
| 14 | `GodelTwoPrf:191‑193` | DUDOSO | ARREGLADO | ✏️ («la teoría no es Q++»). Es la única aparición de «Q++» en los `.lean`. |
| 15 | `Meta/CodeNumeralPrf.lean:32‑33` | HISTÓRICO‑SIN‑MARCA | ARREGLADO | ✏️ reescrita sin indexar el 14‑10 (añade el `Prf ⊥` del `cons` viejo). |
| 16 | `sondeos/AnclaEqInconsistente.lean:16‑17` | HISTÓRICO‑SIN‑MARCA | SIGUE en el fichero | La misma nota ✏️ dice en :12 «instancia `instAnclaEq`», que ADR‑118 retiró. Arreglo: «…`AnclaEq` es TEOREMA (`prf_ancla`; ADR‑118 retiró la clase y `instAnclaEq`)… no prueba que los 142 sean consistentes (✏️ ADR‑120: lo prueba `consistencia`).» |
| 17 | `sondeos/AnclaSoundness.lean:77‑83` | HISTÓRICO‑SIN‑MARCA | SIGUE en el fichero | Añadir a la ✏️ del 04‑10: «✏️ ADR‑119/120: el modelo existe (`MNV V₀`, `MN_axioms`, los 142) y `ConsistentH` es teorema; la sección ⬜ es registro.» |
| 18 | `sondeos/ModeloDiscriminador.lean:5‑8` | HISTÓRICO‑SIN‑MARCA | SIGUE en el fichero | «(✏️ ADR‑120: `ConsistentH` es teorema, `consistencia`; modelo de los 142.)» |
| 19 | `sondeos/PrfBotCodificacionVieja.lean:34‑35` | HISTÓRICO‑SIN‑MARCA | SIGUE en el fichero | «(✏️ ADR‑120: la consistencia la probó el modelo de los 142, `consistencia`.)» |
| 20 | `sondeos/OmegaConsistentRefutable.lean:44‑45` | HISTÓRICO‑SIN‑MARCA | SIGUE en el fichero | «(✏️ ADR‑121: `⊬¬G` salió sin ω‑consistencia ni Rosser: `goedel_I_neg`.)» |

En los cinco sondeos, la única marca es la nota ✏️ ADR‑134 de `sondeos/README.md`; el fichero en sí sigue diciendo lo de antes.

## (b) Comprobación de hallazgos CIERTO o HISTÓRICO‑MARCADO

**Se sostienen (25):**
- `HilbertSeq:435`: el código usa `axioms.getD`.
- `Minimal/Axioms.lean`: :1162‑1164, :1611‑1613, :1677 (`ax21` está en `primAxioms`, `Full/Induction:78`), :443 (`sub` sólo en `ax29`, que es primitivo), :1035 y :1057/:1640/:1655 (CIERTOS); :25‑33, :457, :817, :1701 y :400‑404 (HISTÓRICO‑MARCADO).
- `Hilbert.lean:37‑39` y :151‑152: coinciden con los constructores de :89‑109 y :154‑160, y `ax2`‑`ax5`, `ax8` y `ax9` están en `coreAxioms`.
- `SolidezPrf:13‑17`, `Consistencia:14‑15` y :22‑23, `SolidezVerificador:10‑17`, `GodelTwo:58`, `ReprPrf:39`, `BdAllIntroPrf:46`.
- `Full/Induction:71‑73`, salvo que llama «`Full`» a lo que hoy es `Prf`; `Full/Induction:232`, con el matiz de que es el esquema de `Prf.ind`, no un axioma.
- `check-sorry.bash:410`.
- `InduccionTitulares:39`: el arreglo opcional del censo ya está en el fichero («los cuatro usos de D1 son evitables»).
- `GodelTwo:114‑117` y `ModeloBasura:36‑40` (HISTÓRICO‑MARCADO).

**Reclasifico (6):**
- **`Consistencia:49`, de CIERTO a DUDOSO.** «🏁 Los 142 son CONSISTENTES: `Prf ⊥` no tiene prueba» identifica `ConsistentH` con la consistencia de la lista, que es justo el criterio de DUDOSO del propio censo. Arreglo: «🏁 **`T_Prf` es CONSISTENTE** (los 142 y los esquemas de `Prf`): `MNV V₀` es estándar y satisface los 142 (`estandar_MN`), y `Prf` es sólido en él.»
- **`Meta.lean:17`, de CIERTO a DUDOSO**, por lo mismo («La consistencia de los 142… (`consistencia`)»). Sirve el arreglo del censo.
- **`NatMulPrf:94‑96`: era parcialmente FALSO.** «se probó antes de disponer de `ax6_add_comm`» no es cierto: `ax6` estaba en la lista desde el 2026‑05‑09 y `NatArithPrf` es del 2026‑07‑07. Ya lo corrige una ✏️ del 14‑10 sin indexar (:96‑97), así que queda HISTÓRICO‑MARCADO.
- **`Minimal/Axioms.lean:343‑344`.** Lo de la inducción es cierto, pero la misma línea dice «(sorry pendiente)». No hay ningún `sorry` pendiente, y su gemela :1681 ya pone «(sorry; retirado, ADR‑115)».
- **`sondeos/CantorSobreyectivo.lean:9‑12`, a HISTÓRICO‑SIN‑MARCA.** La frase sobre `listInd` es cierta, pero :10 dice en presente que `ax_L0_cons_def` es «`cons a b = pair a (σb)`». ADR‑113 adoptó la propuesta de este mismo sondeo y no hay ✏️.
- **`Meta.lean:20`** está bien marcado, pero el arreglo que el censo proponía (añadir a la API Gödel I entero, II sin hipótesis y Tarski) sigue sin hacer.

## (c) Omisiones

Prioridad: **A** = falso hoy y relevante; **M** = media; **D** = dudoso; **m** = menor (puntero de línea, cifra o errata).

**Patrones**, para corregir en bloque:
1. **C3/D3 «pendientes».** Lo dicen CantorMonoPrf, NatOrderPrf, NatMulPrf, LineWFAssemblePrf, SubstTreeReflect, HasWitFTrackedPrf, HasWitTrackedPrf, TrackedAtomsPrf, EvalLiftfcPrf, EvalLiftcPrf, D3ChainDotPrf, D3BodyPrf, D3DottedPrf, EvalNthcPrf, EvalArithPrf, ExIntroCodePrf, LineWFGuardPrf, PremsBdAllPrf, CodeCtorKit y CodeTreeReflect. Las evidencias en contra son:
   - `pcc_lineWF_tracked`, `SubstTreeReflect:1151‑1157`, «SIN HIPÓTESIS».
   - `pcc_eval_liftfc`, `EvalLiftfcPrf:1241`.
   - `d3_prf_real` = `d3_prf_of_halves` (`D3ChainDotPrf:1148`), en `PremsBdAllPrf:1300`.
2. **«Nada lo consume todavía» es falso** en 8 bloques `export`.
3. **Vacuidad de la ruta `hI`/`hbI`**, refutables en `sondeos/D3Sigma1Vacuo.lean` (ADR‑132): ReflectionPrf, Sigma1Prf, Sigma1AtomPrf, Sigma1CorePrf y Sigma1BoundedPrf.
4. **Nombres inexistentes citados como vigentes:** `prf_tc_form`, `prf_tc_cons`, `prf_tc_eqc`, `demFormula`, `d3_prf`, `ax_induction`, `prf_tc_objAt`, `prf_hasWitArgs_liftsc`, `bridge_isTC1`, `pcc_eval_substtsc'`, `prf_cantor_mono`, `pcc_forallElim_code`, `instAnclaEq`, `repr_pos'_prfₜ`, `hI_tracked`.
5. **Se omiten las guardas de ADR‑020** en firmas descritas como «códigos arbitrarios»: Sigma1AtomPrf, ForallElimCodePrf, PropCodePrf, ExIntroCodePrf.
6. **Se da la deuda B6b por abierta**, aunque `PrfH_mono` y `PrfH_w1` existen (`HilbertDeduction:76/96`): HasWitFTrackedPrf:183, HasWitTrackedPrf:757, LiftcCodePrf:1426 y EvalLiftfcPrf:749.

### Raíz y barriles
- **`ROBINSON_PlusPlus.lean:13`** · «Meta: Gödelización (Nivel B codificación + Nivel C demostrabilidad). Ver GODEL-STATUS.md» · Falta todo el Nivel D, y GODEL-STATUS.md se declara histórico (:74). → «-- Meta: codificación, `Prf`, D1–D3, el modelo de los 142, `consistencia`, Gödel I/II sin hipótesis y Tarski (estado vivo: NEXT-STEPS.md).» **M**
- **`ROBINSON_PlusPlus.lean:18`** y **`Full/Induction.lean:35‑37`** · «La inducción de la cadena es el constructor `Prf.ind`» · También entra `Prf.listInd`: D2, D3 y Gödel II lo usan (AXIOMS §0.3). → «…los constructores `Prf.ind` y `Prf.listInd`.» **M**
- **`Meta.lean:8‑17`** · La API pública no nombra `consistencia`, `goedel_I`, `goedel_II`, `goedel_I_neg`, `godelCN_indecidible` ni `tarski`, aunque los importa. Junto con :20‑21 sugiere que ⊬¬G no existe. → añadir «· Sin hipótesis: `consistencia`, `goedel_I`, `goedel_II` (Consistencia); `goedel_I_neg`, `godelCN_indecidible` (SolidezVerificador); `tarski`, `tarski_semantico` (TarskiPrf).» **A**

### Meta/

**CantorMonoPrf**
- :33‑35 · «derivable de `ax_induction`, y con ella… los 7 tags de `lineWF` que faltan» · `ax_induction` no existe (hoy es `Prf.ind`) y los 7 tags están cerrados. → «…de `Prf.ind` (`prf_nat_induction`), y con ella los 7 tags que entonces faltaban (hoy `pcc_lineWF_tracked`).» **A**
- :66 · «consumidores previstos» · Ya los tiene: EvalLiftc, EvalSubsttc, EvalSubstfc, LiftcCode, LiftfcWitness, SubstfcWitness y Representability2Prf. **M**
- :68 · «copia local de `NatOrderPrf`» · `PrfH_lt_subst2` vive en ChainPrf:90. **M**

**ChainNegPrf**
- :140‑141 y :203‑207 · «queda el front‑end… que no existe» · Existe: `decodeChainAux_none_first` (:771), y la cabecera lo da por CERRADO en :121. → pasarlo a pasado («quedaba, hasta ADR‑078»). **M**

**CheckArith**
- :30 · «`demFormula`» · No existe; es `provFormulaC` (:66), y la de Gödel, `provFormulaC'` (ProofChain:107). **A**
- :32 · «`numeralM 0..17`» · `validProofFn` llega a 20 (`ax_vpf_ind` 18, `qconf` 19, `listInd` 20). → «0..20». **A**

**CodeCtorKit**
- :49 · «18 tags pendientes» · Ya no queda ninguno. **M**
- :154‑155 · «11 call‑sites en cuatro módulos» · Hoy son unos 30, en 8 módulos. **m**

**CodeDecode**
- :115 · «los 9 tags de fórmula» · Son 8 (del 2 al 9). **m**

**CodeDistinct**
- :38‑39 y :51‑60 · «La dirección negativa (…⊬¬G) reposa sobre que la teoría refuta igualdades de códigos… Descargarla exige ω‑consistencia…» · `goedel_I_neg` sale de `prf_sound` y `prf_of_prov`. Del módulo sólo quedan `charToNat_ne` y `NotFC`/`NotTC`, que sólo usa ChainNegPrf. → «🗑️ (registro, hasta ADR‑121)…» **A**
- :125 · «nueve constructores» · `NotFC` tiene 11. **m**

**CodeNatInjPrf**
- :33 · «`consN a b = triN (a+b+1) + (b+1)`» · Es la fórmula de antes de ADR‑113; hoy `consN a b := triN (a+b) + b + 1` (Axioms:642), como dice el propio :93. **A**

**CodeTreeReflect**
- :52 · «`prf_tc_objAt`» · No existe; es `pcc_tc_objAt` (:225). **m**
- :378‑379 · «lo único que queda por hacer» · Ya está hecho (LineWFPropPrf; C3 cerrado). **D**

**CodeWitnessPrf**
- :41 · «Cero axiomas de Lean» · Su fila de footprint es `[propext, Quot.sound]`; el proyecto ya corrigió esta misma frase en EvalPredPrf:29. → «cero `axiom` del proyecto». **D**
- :1396 · «el análogo del sort FÓRMULA, que no existe» · Existe: `prf_hasWitF_liftfc`. **M**
- :2038 · Cita `Probe/`, que no está versionado. **D**
- :2170‑2173 · Cifras sin fecha («214… 50 de 57»). **m**

**D3BodyPrf**
- :25 · «El reflector, `pcc_lineWF_tracked_modulo_other`» · La prueba usa `pcc_lineWF_tracked` (:115). **A**
- :276‑277 · «consumirá» · Ya lo consume `hB_premsDotAt`. **M**
- :311 · «consumidor previsto» · Ya lo es: `d3_prf_real`. **M**

**D3ChainDotPrf** (además de T32)
- :12‑17, :40‑42, :50‑57 («`pcc_lineWF_tracked`… no existe sin condicionar»), :202‑204, :255‑259, :689‑691, :756, :919‑920, :1010‑1014, :1212‑1224 y :1228‑1232 («Nada consume todavía este módulo»).
- Evidencia: D3 está probada a través de este mismo módulo; `hbody_of_halves` (:1126) se usa en PremsBdAllPrf:1297, y `d3_prf_of_halves` (:1148) es `d3_prf_real`.
- → ✏️ en la cabecera: «D3 PROBADA: `d3_prf_real` = `d3_prf_of_halves` (§13); lo que sigue es registro»; tablas a ✅; y el export, «por CONSUMO: D3BodyPrf, PremsBdAllPrf». **A**

**D3DottedPrf**
- :41‑44 · «hC_dot/hI_dot — siguiente ladrillo» · Están cerrados; D3 pasa por este keystone. **M**

**D3InDotPrf**
- :56 y :375‑376 · «+`prf_tc_form`» · No existe; la prueba usa `prf_tc_form_numeral` y `pcc_to_formCode_imp`. **A**
- :296 · El nombre correcto es `substCodeF_boundedCarcIn_at`. **m**

**DerivCondPrf**
- :26 · «Porte de `Meta/DerivCond.lean`» · Ese módulo se retiró y este fichero no lleva banner. → «(D2 sobre ⊢; retirado, ADR‑115)». **M**

**DiagonalNumeral**
- :52‑54 · «hoy, sólo con `ConsistentH`» · Calla que es teorema y que existe `goedel_I`. **D**

**DiagonalTwo**
- :52‑53 y :89 · «Gödel I es `goedel_first_prf`» · Hoy Gödel I va entero y sin hipótesis: `goedel_I` + `goedel_I_neg` (`godelCN_indecidible`). **A**

**Div2ParityPrf**
- :116 · «Lo consumen L2 y… L3» · L3 no lo usa (lo dice el propio :185). **m**
- :29‑31 · Lo da por pendiente y está cerrado. **D**

**EvalArithPrf**
- :32, :46 y :52 · «base de `+`… el paso inductivo queda para…» · El módulo prueba el paso y `pcc_eval_add` (:536). **A**
- :154‑156 y :547‑548 · «Retira 74 copias» · Las copias siguen en los sondeos. **M**

**EvalLiftcPrf**
- :871‑874 · «Nada lo consume todavía» · Lo consume EvalLiftfcPrf:1205, :1223 y :1226. **A**
- :97‑101 y :850‑854 · «sale a la raíz… los ocho lemas GENÉRICOS» · El export no los saca: bajaron a SubstfcWitness y CodeWitness. **A**
- :884‑891 · «salen con CUATRO» y en la misma línea «hoy no hay cuarto» · Se contradice; son los tres de Lean. **A**
- :51‑63 (29 nombres; hoy 36), :208 (cuatro `rfl`; son cinco), :132‑141 y punteros en :44, :300, :364 y :751. **m**

**EvalLiftfcPrf**
- :6‑9 y :27‑29 · «`pcc_eval_liftfc` es lo único que separa a C3… deja la obligación enunciada» · Este mismo módulo lo prueba (:1241). **A**
- :1252‑1268 · «Ni la mitad TÉRMINO a nivel arbitrario existe» · Existe; :1279 ya dice SALDADA. **M**
- :1312‑1316 · «…cerraría los cuatro tags… Nada lo consume» · SubstTreeReflect:533 lo usa. **A**
- :493 y :918 · «No se descarga en este tramo» · Se descarga en §9.2. **D**

**EvalNthcPrf**
- :55‑59 · «`pcc_nthc_succ_code`… — pendiente… siguiente ladrillo» · Está todo en el fichero: :121 y `pcc_eval_nthc` (:367, que usa PremsBdAllPrf:693). **A**
- :243 y :259 · Sustitución mecánica rota: «sustituto de `pcc_dot_cons` (antes `prf_tc_cons'`…)`». **M**

**EvalRunFnPrf**
- :32‑34 y :44‑45 · «`hI_dot` necesita…» · `hI_dot` ya es teorema (D3InDotPrf:517); `pcc_eval_runFn` no existe y nada lo pide. **M**

**EvalSubstfcPrf**
- :37 · `bridge_isTC1` sólo existe en sondeos. **m**
- :292, :500, :506, :1576 y :1581 · `pcc_eval_substtsc'`, con prima, sólo existe en sondeos. **m**
- :1521‑1523 · «CERO axiomas de Lean… cero hipótesis» · El footprint es `[propext, Classical.choice, Quot.sound]` y el teorema tiene dos hipótesis. → «Footprint: los tres de Lean; ningún `axiom` del proyecto; sólo las dos guardas.» **A**
- :1590 y :1607 · «ningún sondeo consume… consumidor previsto C3» · Lo consume C3 (SubstTreeReflect:471). **M**

**ExIntroCodePrf**
- :31 · «el ensamblaje queda planificado abajo» · Está hecho: `pcc_exIntro_code'` (:79). **A**
- :75‑78 · «(`hAc`, `hw`)… en `d3`» · La firma pide `hwF`/`hwT` (no `hw`), y `d3` no existe. **A**

**ForallElimCodePrf**
- :39‑40 · `prf_lineWF_q1` «arbitrarios» · Pide `hwA` y `hwt` (ReprPrf:785). **A**
- :80‑82 · «Sólo pide `Ac` cerrado» · `_open` pide `hwF`/`hwT`. **A**

**GodelTwo**
- :45‑47 · «hoy su única hipótesis es `ConsistentH`» · Existe `goedel_II` sin hipótesis (Consistencia:57). **A**

**GodelTwoPrf**
- :200‑205 · «con `ConsistentH` desaparecen… los dos esquemas de inducción» · Desaparecen los dos `axiom`, no la inducción: Gödel II usa `ind` y `listInd` como constructores de `Prf` (InduccionTitulares; AXIOMS §0.3). **M**

**HasWitFTrackedPrf**
- :182‑183 · B6b · `PrfH_mono` existe. **A**
- :1192‑1203 · «NO deja `pcc_lineWF_tracked` incondicional… hay 14… Nada lo consume» · Es incondicional, y `pcc_hGuardF` se usa en SubstTreeReflect:779, :813 y :848. **A**

**HasWitTcFnPrf**
- :19 y :411 · `pcc_forallElim_code` no existe (hay `'` y `_open`). **m**

**HasWitTrackedPrf**
- :606‑607 · «lo único que queda» · Lo descargan §8 y §9. **D**
- :757 · B6b. **A**
- :1261‑1266 · «Nada lo consume» · Lo usan HasWitFTracked y SubstTreeReflect (`pcc_hGuardT`); `DEUDA_wfAll1_tracked` está probada en :904. **A**
- :20‑21 y :987 · Punteros a Axioms caducados (hoy :1241 y :1244). **m**

**HilbertDeduction**
- :26‑27 · La lista de constructores omite `listInd`. **M**
- :95 · «el caso que consumen los cuatro módulos» · `PrfH_w1` no lo usa nadie. **A**
- :168 · `provCodeC'_elim` no es una declaración. **m**

**HilbertSeq**
- :411 · «el objeto `demFormula`» · No existe; es `provFormulaC'`. **A**
- :407, :449 y :458 · «Reemplaza el postulado…» · Esos postulados se retiraron en F7a. **D**
- (El título de :160 ya está arreglado sin indexar.)

**InAxiomsCodePrf**
- :62, :76 y :216 · `prf_tc_form` · No existe; el propio fichero dice «murió» en :236. Hoy es `pcc_tc_formCode_internal`. **A**

**LiftcCodePrf**
- :27 · «CONTENIDO EXACTO PROPUESTO» · Ya es el módulo promovido. **M**
- :58‑59 · Colisión con un gemelo que se borró en B8b. **A**
- :227 · «al promover B2…» · Ya se promovió. **M**
- :1426 · B6b. **A**
- :40 (cuatro axiomas; son cinco) · **D**
- Punteros en :53, :613, :655, :760, :1271 y :1297. **m**

**LiftfcWitnessPrf**
- :17 · `prf_hasWitArgs_liftsc (v Y)` · No existe; es `prf_hasWitArgs_liftsc_of (w v Y)` (:357), con otro antecedente. **A**

**LineWFAssemblePrf**
- :32‑40, :89 y :95‑103 · «Los 7 tags que faltan… bloqueados tras `pcc_eval_substfc`… el único trabajo restante» · `pcc_eval_substfc` existe y los 7 están en SubstTreeReflect §8–§10bis. → la marca [HISTÓRICO] que ya lleva LineWFGuardPrf:39. **A**

**LineWFCases**
- :31‑36 · «sus dos consumidores… D3/hC_dot» · Ningún módulo de D3 lo importa. **M**

**LineWFGuardPrf**
- :202 · «LAS DOS OBLIGACIONES QUE QUEDAN» · Están probadas. **M**

**LineWFTrackedPrf**
- :413‑415 · `prf_tc_eqc` · No existe; la prueba usa `PrfH_congr_tcFn` y `pcc_dot_eqc_symm`. **A**
- :610 · «invocará» · Ya lo invoca. **m**

**ListEtaPrf**
- :197 · «Consumidor previsto» · Ya lo consume PremsOfTagPrf:106. **M**

**MpCodePrf**
- :305‑306 · Punteros. **m**

**NatMulPrf**
- :34‑35 · «`prf_cantor_mono`… los 7 tags que faltan» · Son `_left`/`_right`, y los 7 están cerrados. **A**

**NatOrderPrf**
- :33 · «`Derives` tenía la ω‑regla» · Según ADR‑027, `gen` no es la ω‑regla. **A**
- :36‑37 · «7 tags que faltan». **A**

**NumCodeClosedPrf**
- :39 · «`tcFn` sólo tiene `ax_tc_zero`/`ax_tc_succ`/`ax_tc_cons`» · `ax_tc_cons` está fuera de `axioms` desde ADR‑012. **A**

**OmegaReflect**
- :127‑128 · «`isClosed` sigue siendo útil» · No tiene ningún uso. **D**

**PremsBdAllPrf**
- :39‑41 · «una sola obligación abierta, `DEUDA_premsBody`» · La prueba este mismo fichero (:1013), junto con `d3_prf_real` (:1300). **A**

**PremsOfDotPrf**
- :1042 · «Consumidor previsto: B2» · Ya lo consumen D3BodyPrf:225 y PremsBdAllPrf:684. **M**

**PropCodePrf**
- :120‑121 y :27‑29 · `prf_lineWF_ind` «código `a` arbitrario» · Pide `hwa` (ReprPrf:871). **A**

**Provability**
- :23 · «NIVEL C: DEMOSTRABILIDAD (provisional, en construcción)» · Hoy sólo es la codificación. **M**
- :223‑224 · «Hoy Gödel I es `goedel_first_prf`» · Es `godelCN_indecidible`, sin hipótesis. **M**

**ReflectionPrf**
- :34‑36 · Cita `Meta/Reflection.lean` y `d3_prf`, que no existen. **A**
- :41‑45 y :73‑79 · «núcleo duro claramente especificado» · `hI` es refutable, así que `d3_prf_of_sigma1` es vacuo. T05 cubre :44‑45 y :80‑82, no :34‑42. **A**

**ReprPrf**
- :272 · «tres longitudes» · Falta la 2 (`thy`). **m**

**Representability2**
- :42‑45 y los encabezados vacíos :90, :93, :96 y :115 · Anuncian el tracking y D1, pero el fichero sólo tiene el encoder y dos guardas; todo lo demás está en Representability2Prf. **A**

**RunFnBoundedPrf**
- :24‑30 · «SONDEO… Hipótesis a contrastar» · Es producción y la hipótesis está probada en :57. **D**

**Sigma1AtomPrf**
- :337‑341 · «sin axioma de inversión… no es derivable» · `ax_lineWF_inv` está en la lista, `prf_lineWF_inv` está 13 líneas más abajo, y la fórmula es `pcc_lineWF_tracked`. **A**
- :171‑177 · «códigos arbitrarios» · Faltan las guardas. **A**
- :28, :36, :90 y :239 · Remiten a la ruta `hbI`, que es vacua. **M**

**Sigma1BoundedPrf**
- :25 y :32‑42, :76‑82 · Presentan como reducción lo que es vacuo. **A** (el núcleo ya está en T05; :25 y :32‑36, no)

**Sigma1CorePrf**
- :36‑41, :52 y :137 · «El obstáculo de `hI`…» · `hI` es refutable, no hay obstáculo técnico que salvar. **A**

**Sigma1Prf**
- :28‑39 · «necesita aún la inducción object» para `hI` · `hI` es refutable y D3 se cerró por la vía punteada. **A**

**Sigma1TrackedPrf**
- :52 · `prf_tc_cons` «sí computa» · No existe. **A**
- :38‑42 y :53‑56 · «requiere la Opción A de raíz» · La Opción A se descartó; `hI_tracked` no existe. **M**

**SubstTreeReflect**
- :15‑18, :29‑39 y :319 · «⛔ `pcc_eval_liftfc`… bloquea 4 de 7; `STree` trae sólo `sub`» · Ya existe y se usa aquí mismo (:533; :854 «Lo único que faltaba»); `STree` tiene `lift` y `tcm`. **A**
- :1186‑1196 (export) · «entrega tres de los siete… `pcc_eval_liftfc`, que no existe… sigue condicional. Nada lo consume» · Falso en las tres cosas: el módulo entrega los 7 y `pcc_lineWF_tracked`, y lo consumen D3BodyPrf:115 y PremsOfDotPrf:1037. **A**
- :1040‑1042 y :8‑10 · `ind`/`listInd` «a la misma distancia» · Están cerrados. **M**

**SubstfcWitnessPrf**
- :398‑400 · «`prf_nil_or_cons` vive en EvalLiftcPrf, en rojo» · Es al revés: se declara aquí (:422). **A**
- :1481 · «`PrfH_congr_substfc3` vive en BdAllIntroPrf, en ROJO» · Vive en NumCodeClosedPrf:88. **A**
- :543 · «Al promover…» · Ya está promovido. **M**

**TrackedAtomsPrf**
- :643‑647 · «C3 (`DEUDA_hGuardT/F`) y D3 (`DEUDA_chainOkBDot`), ninguno de los cuales existe todavía» · Existen los tres, y el kit lo usan HasWitTracked, HasWitFTracked y D3ChainDot. **A**
- :26 · Puntero. **m**

**TrackedCorePrf**
- :35‑49 y :97 · Plan D1ₜ (`repr_pos'_prfₜ`) · Ese nombre no existe y el plan se descartó el 2026‑07‑09; :46 cita `prf_tc_form`. **M**

**VerifierSound**
- :46‑49 · `axioms ⊢ lineWF ⟨…basura…⟩` presentado en presente · Era una medición sobre ⊢, hoy registro. **M**

### Minimal/Axioms.lean
- **:108‑109** · «π₁(x,y) = \frac{\frac{(x+y)(x+y+1)}{2}+y}{2}» · Divide dos veces. El código es `pair = div2 (cantor_poly) = ((x+y)(x+y+1)+2y)/2` (:115‑134, y :119 lo dice bien); el π₂ no corresponde a nada. → «$π₁(x,y) = \frac{(x+y)(x+y+1)}{2} + y$ (= `cantor_func`)» y quitar :109. **A**
- **:52‑55, :87‑88, :334‑335, :353 y :1679‑1680** · «ahora son defs concretas en Block4_C6_C7… `proj_is_cantor`» / «Son necesarios para las pruebas de C5» · Nada de eso existe. Sus vecinas :1676, :1681 y :1692 sí llevan «(retirado, ADR‑115)». **M**
- **:577** · «etiquetas de regla 0..17» · Son 0..20. **A**
- **:893 y :898** · «Sus 3 ecuaciones» / «la única pieza que falta para la diagonalización» · En la lista hay 2; la diagonal está hecha. **M**
- **:170** · «línea ~441 / ~833» · Hoy son :472 y :918. **m**

### sondeos/ (cabeceras: afirmaciones de presente o notas ✏️ que han envejecido)
- **AnclaEqInconsistente** :12 (`instAnclaEq`) **A**; :72‑73 (`ax_axiomsCodeT_eq`; dice que la inducción sobre `Derives` no vale) **M**.
- **AnclaSoundness** :81‑82 («dos de los 141, dentro de `In`»; hoy son tres de 142 y el ancla lo nombra fuera de `In`) **A**; :61‑64 (M‑11 a la manera vieja, que la ✏️ ADR‑133 no cubre) **M**.
- **CanonNeRefuta** :18‑21 («cons nil nil = … = 2»; hoy es 1) **A**; :35‑36 («Sin medir»; `codeNat_inj` está probada) **A**.
- **CantorSobreyectivo** :10 **A** (ver b).
- **ClassicalChoiceCenso** :65‑68 (raíz `String`, quitada en D7) **A**; :71‑72 (refutado por ADR‑122/131) **M**; :84‑88 (el ⬜ ya está hecho) **A**.
- **CodeNatInj** :37‑45 **A**.
- **D3Sigma1Vacuo** :22‑23 · «Ninguno tiene consumidor» · `d3_prf_of_reflect_bounded` consume a `d3_prf_of_sigma1`. **M**
- **DerivesSinMetaReglas** :16‑18 y :43‑45 (`Derives₀` «sería nuevo»; ya existe) **A**.
- **HenkinSaleDeRaa** :29‑34 y :72‑83 (`raa` y `Completeness` borrados; no compila desde el 2026‑10‑02) **A**.
- **KitPayoff** :27‑36 (`prf_tc_objAt`; hecho como `pcc_tc_objAt`) **A**.
- **Magnitud** :4‑6 · Calcula con el `cons` viejo y compila, así que imprime magnitudes viejas sin avisar. **A**
- **MDiezEnLaFirma** :6‑9 («axioms ⊢ es COMPLETO», en presente) **A**.
- **MedirC_Enmienda** :29‑31 **M**.
- **MedirF_Censo** :82‑84, **MedirF_Opaco** :10/:17‑26 y **MedirF_Replan** :30‑34 · «AxiomListCode en producción», «Todo COMPILA» · **A**.
- **ModeloBasura** :4 · Título «ℕ NO ES MODELO DE `Prf`». **M**
- **ModeloNat** :55‑56 · Control negativo «pendiente» · Está hecho: `control_tc_cons`, ADR‑124. **A** · :62 «(Rosser)». **D**
- **NegVerifierModE** :24‑25 («≐ numeralM 2»; hoy 1) **A**; :29‑44 **M**.
- **NombresFrescosMedicion** :32‑35 **A**.
- **PilotoRastreada** :4‑11 y :28 **A**.
- **PrfHMono** :48‑51 («No los mueve a producción»; ya están) **A**.
- **RecodCoste** :45‑50 **A**; :23‑59 **M**.
- **S1Audit** :2‑4 **A**.
- **S4** :5‑7 **M**.
- **SimbolosSinString** :43‑45 («a una composición de estar limpia»; refutado tras D7) **A**.
- **Patrón: `prf_axiomsCodeT_eq` «la base sancionada»** · DiscriminaEcuacional, DiscriminaTestigoAbierto, ParticionDiscrimina y ParticionTresPredicados (:29 en los cuatro), InTracked:12, KitPayoff:19, ReflectorForallAnidado:39 y A3IsFCBTracked:7. **M**
- **Patrón: «compila» en presente y hoy no** (según `tabla_adr129`) · MedirC_Carga:9, MedirC_Enmienda:5, MedirF_Opaco:10, NegVerifierModE:44, ClausuraNoHaceFalta:10, CanonNeRefuta:21, ReflectorForallAnidado:30, InTracked:65, ParseWitness:57 y HenkinSaleDeRaa:83. **M** (le toca a T10)
- **La nota ✏️ de `sondeos/README.md` no cubre** ModeloBasura:4 ni ModeloNat:55‑62, ni la fila :114 del README.

### Ya en la auditoría y todavía abiertos en el árbol
- **T31:** `CodeWitnessPrf:50‑53`, `Full/Induction:47` («23 primitivos»), `NatMulPrf:158‑160` (anuncia tres puentes; hay dos).
- **T32:** `D3ChainDotPrf:192‑200` y `:1062‑1072`.
- **T05:** los docstrings de `ReflectionPrf:44‑45/:80‑82` y `Sigma1BoundedPrf:38‑42/:76‑87`, todavía sin marcar.

**Las notas ✏️ que añade el índice** las comprobé y son correctas. Entre ellas, la de los 33 símbolos: hay 36 literales `sym!`, menos «…», «[]» y «≤».

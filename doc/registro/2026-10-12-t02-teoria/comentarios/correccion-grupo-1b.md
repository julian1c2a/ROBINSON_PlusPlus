# Corrección de comentarios · grupo 1b (⊬¬G, aritmética, emparejamiento)

**Last updated:** 2026-10-14 — registro (ADR‑134): copia tal cual de lo que se produjo ese día; no se actualiza. La marca está para el control `[E]` de `check-doc-sync.bash`, que mira todo `.md` versionado.

> Registro: el informe final de un agente de sólo lectura, tal cual (fecha: 2026-10-14). Lo que dice del árbol es de esa fecha; lo aplicado, en ADR-134.

## Informe del grupo 1b

Están hechos los 25 hallazgos, en los 11 ficheros de la lista y en ningún otro: 25 corregidos o anotados, ninguno rechazado ni omitido. Además corregí 6 frases falsas nuevas. Todo lo cambiado es texto de comentarios: quité los comentarios de la copia original y de la actual de cada fichero, y el código que queda es idéntico en los 11. No ejecuté lake ni lean, y de git sólo usé órdenes de lectura. Los números de línea son posteriores a la edición.

**Tres hallazgos tenían la premisa en parte equivocada:**
- **1b‑05:** quedan **siete** declaraciones en `CodeDistinct`, no tres: también `formTag`, `termTag` y sus dos `_eq_cons`. Ninguna se usa en código fuera de ese fichero. `ChainNegPrf` sólo nombra `NotFC`/`NotTC` dentro de comentarios.
- **1b‑03:** el front‑end no llegó «con ADR‑078». Entró el mismo 2026‑09‑21, en el commit `01ef473`, después de ADR‑075. El cambio de cota no hizo falta (`0651c1e`).
- **1b‑29:** los consumidores son **seis**, no siete. `LiftcCodePrf` sólo los nombra en un comentario (:1629).

### Hallazgos

**1b‑01** · `ChainNegPrf.lean:50‑52` · **NOTA**
- Evidencia: `goedel_I_neg` está en `SolidezVerificador.lean:558`. El cierre de importaciones de `SolidezVerificador` (104 módulos) no contiene `ChainNegPrf`; sólo `Meta.lean` lo importa.
- Texto nuevo:
  ```
  (✏️ 2026‑10‑14, ADR‑134: la tiene desde ADR‑121, por otra vía y sin este módulo:
  `goedel_I_neg : ¬ Prf (neg godelCN)` (`Meta/SolidezVerificador.lean`), por la solidez del verificador en el
  modelo `MNV V₀`.)
  ```

**1b‑02** · `ChainNegPrf.lean:33‑35` · **NOTA**
- Evidencia: la misma de 1b‑01, más la T66 en `doc/AUDITORIA-SUELO-2026-10-12.md:869`.
- Texto nuevo:
  ```
  > (✏️ 2026‑10‑14, ADR‑134: `⊬¬G` ya está sobre `Prf` desde ADR‑121, y sin este módulo: `goedel_I_neg`
  > (`Meta/SolidezVerificador.lean`), que no lo importa. Ese disparador se cumplió; lo que queda es decidir qué
  > hereda Rosser (⬜, T01) y retirar el resto (T66 de `doc/AUDITORIA-SUELO-2026-10-12.md`).)
  ```

**1b‑03** · `ChainNegPrf.lean:150‑152` y `:216‑218` · **NOTA** (dos)
- Evidencia: `decodeChainAux_none_first` está en `ChainNegPrf.lean:782`. El commit `01ef473` (2026‑09‑21) la introdujo. El commit `0651c1e` (2026‑09‑21) dice que el «cambio de cota» NO hacía falta: `derives_not_boundedCarcLt` se probó sobre `⊢` y se retiró con ADR‑115.
- Texto nuevo en :150:
  ```
  (✏️ 2026‑10‑14, ADR‑134: las dos se resolvieron el mismo 2026‑09‑21. El front‑end es
  `decodeChainAux_none_first` (§2bis, commit `01ef473`), y el cambio de cota no hizo falta: la cota se refutó
  por inducción directa, `derives_not_boundedCarcLt` (`0651c1e`), sobre `⊢` y retirado con ADR‑115.)
  ```
- Texto nuevo en :216:
  ```
  (✏️ 2026‑10‑14, ADR‑134: registro. El front‑end existe desde el mismo 2026‑09‑21,
  `decodeChainAux_none_first` (§2bis), y el cambio de cota no hizo falta: véase la nota al final de la
  cabecera.)
  ```

**1b‑04** · `CodeDistinct.lean:69‑70` · **NOTA**
- Ojo: `CodeDistinct` sí está en el cierre de importaciones de `SolidezVerificador` (le llega por GodelTwoPrf → LineWFCases). Pero ninguna de sus declaraciones se usa, por eso escribí «de ninguna declaración» en lugar de «de este módulo».
- Texto nuevo:
  ```
  (✏️ 2026‑10‑14, ADR‑134: lo tiene desde ADR‑121, `goedel_I_neg`;
  sale del modelo estándar, no de la ω‑consistencia ni de ninguna declaración de este módulo.)
  ```

**1b‑05** · `CodeDistinct.lean:38‑43` · **NOTA** de cabecera del bloque
- Evidencia: un `git grep -w` de las siete declaraciones en todo el repositorio y en `../FOL`. Las menciones de `ChainNegPrf` (:103, :1281…:1452) y de `ReprPrf:998` están todas dentro de comentarios; lo comprobé contando la profundidad de comentario.
- Texto nuevo:
  ```
  ✏️ 2026‑10‑14 (ADR‑134): registro — la mitad `⊬¬G` es hoy `goedel_I_neg` (`Meta/SolidezVerificador.lean`,
  ADR‑121), por la solidez de `Prf` en el modelo estándar `MNV V₀` (`prf_sound`, `prf_of_prov`): sin
  ω‑consistencia y sin que la teoría refute igualdades de códigos. De este módulo quedan siete declaraciones
  (`charToNat_ne`, `formTag`, `termTag`, sus dos `_eq_cons`, `NotFC`, `NotTC`), y ninguna se usa en código
  fuera de este fichero (grep del 2026‑10‑14; `ChainNegPrf` y `ReprPrf` sólo las nombran en comentarios).
  Lo que sigue describe el plan de antes de ADR‑121.
  ```

**1b‑06** · `CodeDistinct.lean:133‑134` · **NOTA** (era cierto al escribirse)
- Evidencia: `NotFC` tenía 9 constructores en `71809fa` (ADR‑095) y tiene 11 desde `cd5807b` (ADR‑096).
- Texto nuevo: `(✏️ 2026‑10‑14: once desde ADR‑096, con los dos` / `` `eqc*` de abajo) ``

**1b‑07** · `OmegaReflect.lean:48‑50` · **NOTA**
- Evidencia: `OmegaReflect` no está en el cierre de importaciones de `SolidezVerificador`.
- Texto nuevo:
  ```
  (✏️ 2026‑10‑14, ADR‑134: la mitad `⊬¬G` está sobre `Prf` desde
  ADR‑121, `goedel_I_neg` en `Meta/SolidezVerificador.lean`, sin ω‑consistencia ni Rosser y sin este módulo,
  que no importa. Rosser —`⊬R ∧ ⊬¬R` sólo con la consistencia— sigue ⬜, T01.)
  ```

**1b‑08** · `OmegaReflect.lean:130‑133` · **CORREGIDO** (error de cualquier fecha)
- Evidencia: `isClosed` (`OmegaReflect.lean:142`) no tiene ningún uso hoy, y tampoco lo tenía en `5f98a56`, cuando se escribió la frase. Los 5 sondeos que citan `IsCodeShaped` (CanonNeRefuta, MedirF_Censo, MedirF_Opaco, MedirF_Replan, NegVerifierModE) tienen rc 1 en `tabla_adr129.txt`.
- Texto nuevo:
  ```
  porque los sondeos la citan. (✏️ 2026‑10‑14: decía también «porque `isClosed` (abajo) sigue siendo
  útil»; `isClosed` no tiene ningún uso (grep del 2026‑10‑14), y los cinco sondeos que citan la clase no
  compilan: rc 1 en `sondeos/pasadas/tabla_adr129.txt`, medido el 2026‑10‑05.)
  ```

**1b‑09** · `VerifierSound.lean:132‑133` · **NOTA**
- Evidencia: `VerifierSound` no está en el cierre de importaciones de `SolidezVerificador`.
- Texto nuevo:
  ```
  (✏️ 2026‑10‑14,
  ADR‑134: la tiene desde ADR‑121, `goedel_I_neg` en `Meta/SolidezVerificador.lean`, que no usa este módulo.)
  ```

**1b‑10** · `VerifierSound.lean:48‑49` · **NOTA**
- Evidencia: `tabla_adr129.txt:55` da `NegVerifierModE` con rc 1.
- Texto nuevo:
  ```
  (✏️ 2026‑10‑14, ADR‑134: registro; se midió sobre `⊢`, retirado con
  ADR‑115, y `sondeos/NegVerifierModE.lean` ya no compila)
  ```

**1b‑20** · `CheckArith.lean:30‑32` · **CORREGIDO** con «decía»
- Evidencia: `git log -S "def demFormula"` sale vacío; el nombre sólo aparece como plan en `GODEL-D-ARITHMETIZATION.md:187`. La definición real es `provFormulaC` (`CheckArith.lean:70`), y la de Gödel es `provFormulaC'` (`ProofChain.lean:107`).
- Texto nuevo:
  ```
  `provFormulaC` (la fórmula Σ₁ de demostrabilidad; ✏️ 2026‑10‑14: decía `demFormula`, el
  nombre del plan, que no llegó a existir; la de Gödel es `provFormulaC'`, `Meta/ProofChain.lean`)
  ```

**1b‑21** · `CheckArith.lean:34‑36` · **NOTA**
- Evidencia: `ax_vpf_ind` (18), `ax_vpf_qconf` (19) y `ax_vpf_listInd` (20) están en `Minimal/Axioms.lean:1185/1193/1199`; no hay ninguna etiqueta por encima de 20. Los números de línea de las instrucciones (1173‑1187) se han movido, así que cité por símbolo.
- Texto nuevo:
  ```
  ; ✏️ 2026‑10‑14, ADR‑134: hoy `0..20`, con 18 =
  `ax_vpf_ind`, 19 = `ax_vpf_qconf` y 20 = `ax_vpf_listInd`, en `Minimal/Axioms.lean`
  ```

**1b‑22** · `CodeNatInjPrf.lean:33‑36` · **NOTA** (era cierto al escribirse, no un error de contenido)
- Evidencia: cuando se escribió la línea (`e46e482`, 2026‑09‑02) la definición era `consN a b := triN (a + (b + 1)) + (b + 1)` (`CodeNumeralPrf.lean:65`). Hoy está en `Minimal/Axioms.lean:651`.
- Texto nuevo:
  ```
  (✏️ 2026‑10‑14, ADR‑134: ésa era la de antes de ADR‑113, con
  `cons a b = pair a (σ b)`; hoy `consN a b := triN (a + b) + b + 1`, en `Minimal/Axioms.lean`, como dice
  el docstring de `consN_inj`).
  ```

**1b‑23** · `NumCodeClosedPrf.lean:46‑48` · **NOTA** (la puse después de la lista de viñetas)
- Evidencia: `Axioms.lean:1638` («ax_tc_cons RETIRADO»), `control_tc_cons` en `ModeloCodificacion.lean:391`, y el texto es del 2026‑07‑10, anterior a ADR‑012.
- Texto nuevo:
  ```
  (✏️ 2026‑10‑14, ADR‑134: `ax_tc_cons` está fuera de la lista `axioms` desde ADR‑012 —daba `axioms ⊢ ⊥`—, y
  el modelo lo refuta, `control_tc_cons` en `Meta/ModeloCodificacion.lean`, ADR‑124; hoy las ecuaciones de
  `tcFn` son sólo `ax_tc_zero` y `ax_tc_succ`.)
  ```

**1b‑24** · `NatOrderPrf.lean:33‑35` · **CORREGIDO** con «decía»
- Evidencia: ADR‑027 (`DECISIONS.md:1966`): «La fuerza del cálculo no viene de `gen`: viene de `raa` e `imp_intro`».
- Texto nuevo:
  ```
  (`Derives` era más fuerte: su fuerza venía de `raa` e `imp_intro`, no de
  `gen`, ADR‑027; sólo existía `prf_to_derives`, también retirado; ✏️ 2026‑10‑14: decía «`Derives` tenía la
  ω‑regla», y `gen` no lo es)
  ```

**1b‑25** · `NatOrderPrf.lean:38‑39` · **NOTA**
- Evidencia: `SubstTreeReflect.lean:1157`, cuyo docstring dice «los siete de sustitución».
- Texto nuevo:
  ```
  (✏️ 2026‑10‑14, ADR‑134: cerrados; C3 lo está
  desde el 2026‑09‑10, `pcc_lineWF_tracked` en `Meta/SubstTreeReflect.lean`, los 21 tags sin hipótesis.)
  ```

**1b‑26** · `NatMulPrf.lean:35‑37` · **NOTA**
- Evidencia: `CantorMonoPrf.lean:325/330`.
- Texto nuevo:
  ```
  (✏️ 2026‑10‑14, ADR‑134: hecho; la monotonía
  quedó como `prf_cantor_mono_left`/`prf_cantor_mono_right` en `Meta/CantorMonoPrf.lean`, y los 7 tags están
  cerrados desde el 2026‑09‑10: `pcc_lineWF_tracked`, en `Meta/SubstTreeReflect.lean`.)
  ```

**1b‑27** · `NatMulPrf.lean:162‑164` · **CORREGIDO** con «decía»
- Evidencia: sólo existen dos puentes, `prf_div_mod_eq` y `prf_mod2_range`. `git log -S "ax24_mod2_of_even ∈ axioms"` sale vacío; fuera de `Axioms.lean` sólo está el `v_ax24` semántico (`ModeloEstandar.lean:359`).
- Texto nuevo:
  ```
  Los dos son instanciación directa: `ax17_div_mod_eq` y `ax21_mod2_range` están en la lista `axioms`.
  (✏️ 2026‑10‑14: decía «los tres», con `ax24_mod2_of_even`, que también está en la lista, pero su
  puente no se escribió aquí ni en otro módulo.)
  ```

**1b‑28** · `CantorMonoPrf.lean:36‑38` · **NOTA**
- Evidencia: el 2026‑07‑23 (`305a349`) `ax_induction` era un axioma de `Full/Induction.lean:166`; hoy no existe. El constructor es `Hilbert.lean:156` (`ind`), y `prf_nat_induction` está en `NatArithPrf.lean:54`.
- Texto nuevo:
  ```
  (✏️ 2026‑10‑14, ADR‑134: `ax_induction` era el axioma de `⊢`, retirado con ADR‑115; en `Prf` la inducción es
  el constructor `Prf.ind` (`prf_nat_induction`, `Meta/NatArithPrf.lean`), y los 7 tags están cerrados desde
  el 2026‑09‑10: `pcc_lineWF_tracked`, en `Meta/SubstTreeReflect.lean`.)
  ```

**1b‑29** · `CantorMonoPrf.lean:69‑71` · **NOTA**
- Evidencia: usos en código en `EvalLiftcPrf:433`, `EvalSubstfcPrf:452`, `EvalSubsttcPrf:1157`, `LiftfcWitnessPrf:230`, `SubstfcWitnessPrf:368` y `Representability2Prf:173`.
- Texto nuevo:
  ```
  ; ✏️ 2026‑10‑14, ADR‑134: ya no son
    previstos: la usan en código `EvalLiftcPrf`, `EvalSubsttcPrf`, `EvalSubstfcPrf`, `LiftfcWitnessPrf`,
    `SubstfcWitnessPrf` y `Representability2Prf`
  ```

**1b‑30** · `CantorMonoPrf.lean:73‑74` · **NOTA** (era cierto al escribirse)
- Evidencia: `NatOrderPrf` tuvo su copia desde `82b9207` (2026‑07‑23) hasta el dedup `5891d06` (2026‑09‑09). Hoy la única está en `ChainPrf.lean:90`, que llega a `CantorMonoPrf` por las importaciones.
- Texto nuevo:
  ```
  ✏️ 2026‑10‑14: desde el dedup del
    2026‑09‑09, `5891d06`, la única copia vive en `Meta/ChainPrf.lean`, que llega aquí por los imports.
  ```

**1b‑31** · `CodeDecode.lean:115` · **CORREGIDO** (errata, sin nota)
- Evidencia: las ramas de `decodeForm` son `some 2`…`some 9` (:120‑148).
- Texto nuevo: `(los 8 tags de fórmula, del 2 al 9)`

### NUEVAS (mismas reglas)

- **N1** · `ChainNegPrf.lean:116` · puntero desplazado: `Meta/CodeDecode.lean:80,115` pasa a `Meta/CodeDecode.lean`. Las definiciones están en :81 y :116, y la frase ya nombra los dos símbolos.
- **N2** · `CodeDecode.lean:170‑172` · NOTA sobre «Es la pieza que hace el trabajo en `VerifierSound`». En el código, `decodeForm_inj` sólo se usa en `decodeLine_carc` (`ChainNegPrf.lean:724`). `verifier_sound` es `decodeChain_prf` (`ChainDecode.lean:406‑409`), que no pasa por él, y `git log -S` muestra que nunca se usó en `VerifierSound` ni en `ChainDecode`. Texto nuevo:
  ```
  (✏️ 2026‑10‑14, ADR‑134: medido,
  `VerifierSound` no lo usa —`verifier_sound` es `decodeChain_prf`, de `Meta/ChainDecode.lean`, que no pasa por
  `decodeForm_inj`—; su único consumidor en el build es `decodeLine_carc`, en `Meta/ChainNegPrf.lean`.)
  ```
- **N3** · `VerifierSound.lean:41‑42` · la misma afirmación («La pieza que lo hace gratis es `decodeForm_inj`»). Texto nuevo:
  ```
  (✏️ 2026‑10‑14, ADR‑134: medido, `verifier_sound` no lo usa: es `decodeChain_prf`, que no pasa por
  `decodeForm_inj`; quien lo usa es `decodeLine_carc`, en `Meta/ChainNegPrf.lean`.)
  ```
- **N4** · `OmegaReflect.lean:58‑59` · «la ω‑regla `gen`» pasa a «la regla `gen` (✏️ 2026‑10‑14: decía «la ω‑regla `gen`»; no lo es, ADR‑027)».
- **N5** · `CodeNatInjPrf.lean:56‑58` · «Las cinco meta-reglas ω» pasa a «Las cuatro meta-reglas». El footprint citado en :52‑54 tiene cuatro `MetaRules` más `ax_induction`. Se añade: «(✏️ 2026‑10‑14: decía «las cinco meta-reglas ω»: en la lista de arriba son cuatro, y `gen` no es la ω‑regla, ADR‑027.)»
- **N6** · `CantorMonoPrf.lean:66` · puntero desplazado: `Meta/BdAllIntroPrf.lean:295` pasa a `Meta/BdAllIntroPrf.lean` (`prf_lt_succ_self` está hoy en :292).

Hay una frase caducada que dejé sin tocar: `ChainNegPrf.lean:86‑93` cita en presente `ax_axiomsCodeT_eq`, un axioma de `⊢` retirado en `b1dedd1`. Está dentro del bloque que la propia cabecera declara REGISTRO (:55‑56).

### Ficheros tocados

`git diff --stat` compara el árbol con el índice. En `NatMulPrf` incluye un cambio previo que no es mío (la nota de :98, 2+/1−) y que dejé intacto. El cambio que `NatOrderPrf` ya tenía en el índice tampoco lo toqué.

| fichero (`ROBINSON_PlusPlus/Meta/`) | `git diff --stat` | `/-` antes→después | `-/` antes→después | finales de línea |
|---|---|---|---|---|
| ChainNegPrf.lean | 13+, 2− | 85→85 | 85→85 | CRLF |
| CodeDistinct.lean | 11+, 2− | 10→10 | 10→10 | CRLF |
| OmegaReflect.lean | 8+, 3− | 22→22 | 22→22 | CRLF |
| VerifierSound.lean | 6+, 2− | 15→15 | 15→15 | CRLF |
| CheckArith.lean | 6+, 2− | 7→7 | 7→7 | CRLF |
| CodeNatInjPrf.lean | 6+, 3− | 9→9 | 9→9 | CRLF |
| NumCodeClosedPrf.lean | 4+ | 23→23 | 23→23 | LF, como el original |
| NatOrderPrf.lean | 5+, 3− | 31→31 | 31→31 | CRLF |
| NatMulPrf.lean | 8+, 4− (mías 6+, 3−) | 31→31 | 31→31 | CRLF |
| CantorMonoPrf.lean | 9+, 3− | 40→40 | 40→40 | CRLF |
| CodeDecode.lean | 4+, 2− | 15→15 | 15→15 | CRLF |

Otras comprobaciones: ninguna línea añadida tiene un número impar de acentos graves ni pasa de 124 columnas. Las copias de partida, los specs y los scripts de reemplazo y verificación están en `scratchpad/suelo/comentarios/g1b/`.

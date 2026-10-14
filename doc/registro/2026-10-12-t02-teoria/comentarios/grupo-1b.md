# Grupo 1b · la mitad ⊬¬G que «no existía», la aritmética y el emparejamiento

**Last updated:** 2026-10-14 — registro (ADR‑134): copia tal cual de lo que se produjo ese día; no se actualiza. La marca está para el control `[E]` de `check-doc-sync.bash`, que mira todo `.md` versionado.

Ficheros (sólo éstos), en `ROBINSON_PlusPlus/Meta/`: `ChainNegPrf.lean`, `CodeDistinct.lean`, `OmegaReflect.lean`,
`VerifierSound.lean`, `CheckArith.lean`, `CodeNatInjPrf.lean`, `NumCodeClosedPrf.lean`, `NatOrderPrf.lean`,
`NatMulPrf.lean`, `CantorMonoPrf.lean`, `CodeDecode.lean`.

Prioridad: A = falso hoy y relevante; M = media; D = dudoso; m = menor.

## «⊬¬G no tiene formulación sobre `Prf`» (falso desde ADR‑121)
- 1b‑01 · `ChainNegPrf.lean:46` · → «⇒ Hoy `NegVerifier` no existe; la mitad `⊬¬G` está sobre `Prf` desde ADR‑121
  por otra vía, sin este módulo: `goedel_I_neg` (`Meta/SolidezVerificador.lean`, la solidez en `MNV V₀`).» **A**
- 1b‑02 · `ChainNegPrf.lean:30‑32` · → «…`⊬¬G` ya está sobre `Prf` sin él (`goedel_I_neg`, ADR‑121): borrarlo o
  portarlo a Rosser (⬜); hasta entonces es guía de casos.» (T66 de la auditoría propone retirar el subárbol
  CodeDecode→…→ChainNegPrf cuando Rosser decida qué hereda.) **A**
- 1b‑03 · `ChainNegPrf.lean:140‑141` y `:203‑207` · «queda el front‑end… que no existe» · Existe:
  `decodeChainAux_none_first` (≈ :771), y la cabecera lo da por CERRADO en :121. → pasarlo a pasado («quedaba,
  hasta ADR‑078»; compruébalo). **M**
- 1b‑04 · `CodeDistinct.lean:61‑62` · → «(✏️ 2026‑10‑14, ADR‑134: la mitad `⊬¬G` es hoy `goedel_I_neg`; sale del
  modelo estándar, no de la ω‑consistencia ni de este módulo.)» **A**
- 1b‑05 · `CodeDistinct.lean:38‑39` y `:51‑60` · «La dirección negativa (…⊬¬G) reposa sobre que la teoría refuta
  igualdades de códigos… Descargarla exige ω‑consistencia…» · `goedel_I_neg` sale de `prf_sound` y `prf_of_prov`.
  Del módulo sólo quedan `charToNat_ne` y `NotFC`/`NotTC`, que sólo usa ChainNegPrf (compruébalo). → «🗑️ (registro,
  hasta ADR‑121)…» **A**
- 1b‑06 · `CodeDistinct.lean:125` · «nueve constructores» · `NotFC` tiene 11 (cuéntalos). **m**
- 1b‑07 · `OmegaReflect.lean:46‑48` · → «La mitad `⊬¬G` está sobre `Prf` desde ADR‑121 (`goedel_I_neg`, sin
  ω‑consistencia ni Rosser); la ω‑consistencia de antes tampoco vale sobre `Prf`…» **A**
- 1b‑08 · `OmegaReflect.lean:127‑128` · «`isClosed` sigue siendo útil» · No tiene ningún uso (compruébalo). **D**
- 1b‑09 · `VerifierSound.lean:128‑129` · → «…retirados con ADR‑115. (✏️ 2026‑10‑14, ADR‑134: la mitad `⊬¬G` es hoy
  `goedel_I_neg` y no usa este módulo.)» **A**
- 1b‑10 · `VerifierSound.lean:46‑49` · `axioms ⊢ lineWF ⟨…basura…⟩` presentado en presente · Era una medición sobre ⊢,
  hoy registro (ADR‑115). **M**

## Aritmética, códigos, emparejamiento
- 1b‑20 · `CheckArith.lean:30` · «`demFormula`» · No existe; es `provFormulaC` (≈ :66), y la de Gödel,
  `provFormulaC'` (ProofChain ≈ :107). **A**
- 1b‑21 · `CheckArith.lean:32` · «`numeralM 0..17`» · `validProofFn` llega a 20 (`ax_vpf_ind` 18, `qconf` 19,
  `listInd` 20). → «0..20». **A**
- 1b‑22 · `CodeNatInjPrf.lean:33` · «`consN a b = triN (a+b+1) + (b+1)`» · Es la fórmula de antes de ADR‑113; hoy
  `consN a b := triN (a+b) + b + 1` (`Minimal/Axioms.lean:642`), como dice el propio :93. Error de contenido. **A**
- 1b‑23 · `NumCodeClosedPrf.lean:39` · «`tcFn` sólo tiene `ax_tc_zero`/`ax_tc_succ`/`ax_tc_cons`» · `ax_tc_cons` está
  fuera de `axioms` desde ADR‑012 (y el modelo lo refuta, `control_tc_cons`, ADR‑124). **A**
- 1b‑24 · `NatOrderPrf.lean:33` · «`Derives` tenía la ω‑regla» · Según ADR‑027, `gen` no es la ω‑regla. **A**
- 1b‑25 · `NatOrderPrf.lean:36‑37` · «7 tags que faltan» · cerrados (C3, `pcc_lineWF_tracked`, 2026‑09‑10). **A**
- 1b‑26 · `NatMulPrf.lean:34‑35` · «`prf_cantor_mono`… los 7 tags que faltan» · Son `_left`/`_right` (compruébalo), y
  los 7 están cerrados. **A**
- 1b‑27 · `NatMulPrf.lean:157‑160` (T31) · anuncia tres puentes (ax17, ax21, ax24) y sólo hay dos (compruébalo). **M**
- 1b‑28 · `CantorMonoPrf.lean:33‑35` · «derivable de `ax_induction`, y con ella… los 7 tags de `lineWF` que faltan» ·
  `ax_induction` no existe (hoy es `Prf.ind`) y los 7 tags están cerrados. → «…de `Prf.ind` (`prf_nat_induction`), y
  con ella los 7 tags que entonces faltaban (hoy `pcc_lineWF_tracked`).» **A**
- 1b‑29 · `CantorMonoPrf.lean:66` · «consumidores previstos» · ya los tiene (EvalLiftc, EvalSubsttc, EvalSubstfc,
  LiftcCode, LiftfcWitness, SubstfcWitness, Representability2Prf: compruébalo). **M**
- 1b‑30 · `CantorMonoPrf.lean:68` · «copia local de `NatOrderPrf`» · `PrfH_lt_subst2` vive en ChainPrf (≈ :90). **M**
- 1b‑31 · `CodeDecode.lean:115` · «los 9 tags de fórmula» · Son 8 (del 2 al 9; compruébalo). **m**

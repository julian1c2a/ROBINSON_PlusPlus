# Corrección de comentarios · grupo 4a (testigos rastreados, reflexión Σ₁)

**Last updated:** 2026-10-14 — registro (ADR‑134): copia tal cual de lo que se produjo ese día; no se actualiza. La marca está para el control `[E]` de `check-doc-sync.bash`, que mira todo `.md` versionado.

> Registro: el informe final de un agente de sólo lectura, tal cual (fecha: 2026-10-14). Lo que dice del árbol es de esa fecha; lo aplicado, en ADR-134.

# Informe del grupo 4a: los 21 hallazgos

Los 21 se sostienen y los he corregido. Los 11 ficheros mantienen el mismo número de `/-` y `-/`, la codificación y los finales de línea (CR = LF en los CRLF, CR = 0 en los LF). Solo he tocado comentarios y docstrings. No he ejecutado lake ni lean, así que falta tu compilación. De git solo he usado comandos de lectura.

En cuatro casos el verificador se equivocaba en un detalle, aunque el hallazgo en sí se sostiene:
- **4a‑11:** el plan D1ₜ no se descartó el 2026‑07‑09. Se descartó en la sesión 2026‑07‑05c (§11.2, commit `e08a1e2`, del 2026‑07‑06). El 2026‑07‑09 es solo la línea de estado final del documento de diseño.
- **4a‑06:** los punteros `:1231`/`:1228` eran correctos en HEAD. Solo se desplazan en el árbol de trabajo (T02 en el índice más las ediciones de otros agentes), por eso los he pasado a símbolo.
- **4a‑02:** `pcc_hGuardF` se usa 7 veces en SubstTreeReflect (:779, :813, :848, :883, :916, :1021, :1031), no 3.
- **4a‑20:** `prf_tc_cons` sí existió (de `a0b4bd2`, 2026‑07‑04, a `6f66e61`, 2026‑08‑18). Es un caso (A), no un nombre que nunca existió.

Todas las rutas son relativas a `E:/dropbox/github/lean4/ROBINSON_PlusPlus/ROBINSON_PlusPlus/Meta/`. Las líneas son las de después de editar.

## Por hallazgo

**4a‑01** · `HasWitFTrackedPrf.lean:185` · NOTA.
- Evidencia: `HilbertDeduction.lean:76/96` (`PrfH_mono`, `PrfH_w1`), «saldada el 2026‑09‑11».
- La línea 183, que cita HilbertDeduction:62, no se ha movido.
- Texto añadido tras «…lo hace una vez.»: «(✏️ 2026‑10‑14, ADR‑134: la deuda B6b se saldó el 2026‑09‑11: `PrfH_mono` y `PrfH_w1` (`Meta/HilbertDeduction.lean`) dan hoy ese debilitamiento; el rodeo sigue siendo correcto, sólo ya no es obligado.)»

**4a‑02** · `HasWitFTrackedPrf.lean:1196` (cabecera del export) · NOTA.
- Evidencia: `pcc_lineWF_tracked (t : Term)` no tiene hipótesis (`SubstTreeReflect.lean:1157`) y lo cerró `9a608c9`, del 2026‑09‑10. SubstTreeReflect:1 importa este módulo y usa `pcc_hGuardF` en los siete `_imp`.
- Medido con `git grep`: `hGuard_of_slots` solo aparece en un comentario, LineWFGuardPrf:38.
- Texto: «✏️ 2026‑10‑14 (ADR‑134): registro — desde el 2026‑09‑10 (C3 cerrado) `pcc_lineWF_tracked` (`Meta/SubstTreeReflect.lean`) es INCONDICIONAL: los 21 tags, con los siete de sustitución en §10 y §10bis de ese módulo. Y este módulo SÍ tiene consumidor: `SubstTreeReflect` lo importa y usa `pcc_hGuardF` en esos siete reflectores; `hGuard_of_slots` sigue sin uso en código. Lo que sigue describe el estado del 2026‑09‑07.»

**4a‑03** · `HasWitTrackedPrf.lean:610` · NOTA.
- Evidencia: la frase se escribió en `15cf6d7`, antes de que `0f9bef8` probara `hbody_wfAll1` (:871). Lo aplican `pcc_wfAll1_tracked` y `DEUDA_wfAll1_tracked_proved` (§9).
- Texto: «(✏️ 2026‑10‑14, ADR‑134: ya no queda: la prueba `hbody_wfAll1` (§8), y §9 la aplica en `pcc_wfAll1_tracked` y `DEUDA_wfAll1_tracked_proved`.)»

**4a‑04** · `HasWitTrackedPrf.lean:762` · NOTA.
- Evidencia: la misma que 4a‑01.
- Texto: «(✏️ 2026‑10‑14, ADR‑134: B6b se saldó el 2026‑09‑11 —`PrfH_mono` y `PrfH_w1`, `Meta/HilbertDeduction.lean`—; el rodeo sigue siendo correcto, sólo ya no es obligado.)»

**4a‑05** · `HasWitTrackedPrf.lean:1269` · NOTA.
- Evidencia: `DEUDA_wfAll1_tracked_proved` está en el propio módulo. HasWitFTrackedPrf:1 lo importa y lo usa en código (:120, :344, :865, :1179).
- SubstTreeReflect lo usa en :779, :813 y :848‑849, que son los tags 9, 10 y 13.
- Texto: «✏️ 2026‑10‑14 (ADR‑134): registro — `DEUDA_wfAll1_tracked` está probada en este mismo módulo (`DEUDA_wfAll1_tracked_proved`, §9), y el módulo SÍ tiene consumidores: lo importa `Meta/HasWitFTrackedPrf.lean`, que reusa sus formas (`shapeFCun`/`shapeFCbin`), `pcc_wfAll1_trackedC`, `pcc_argsIn_trackedC` y `pcc_hGuardT`, y `Meta/SubstTreeReflect.lean` usa `pcc_hGuardT` en los reflectores de los tags 9, 10 y 13. Lo que sigue describe el estado del 2026‑09‑07.»

**4a‑06** · `HasWitTrackedPrf.lean:20‑21` y `:993` · CORREGIDO (puntero, sin nota).
- Evidencia: en el árbol actual, `def isTC1` está en `Minimal/Axioms.lean:1241` y `def hasWit` en `:1244`.
- Texto: «(`Minimal/Axioms.lean`, `def hasWit`)», «(`Minimal/Axioms.lean`, `def isTC1`)», y en :993 «(`Minimal/Axioms.lean`, `def hasWit`)».

**4a‑07** · `HasWitTrackedPrf.lean:27` y `TrackedAtomsPrf.lean:35` · NOTA. La cita se conserva.
- Evidencia: `A3IsFCBTracked.lean|1|…|:355: Type mismatch` en las cuatro tablas de `sondeos/pasadas/` (adr121, adr127, d7_antes_de_migrar, adr129).
- Texto en HasWitTracked: «(✏️ 2026‑10‑14, ADR‑134: el sondeo es hoy registro: no compila —rc 1, error en su :355— en ninguna de las cuatro tablas de `sondeos/pasadas/`, la última `tabla_adr129.txt`, medida el 2026‑10‑05; su kit genérico vive en `Meta/TrackedAtomsPrf.lean`.)»
- En TrackedAtoms, el mismo texto, terminado en «…lo que de él sirve es este kit.)».

**4a‑08** · `HasWitTcFnPrf.lean:20` y `:411` · CORREGIDO (errata, sin nota).
- Evidencia: `git log -S "theorem pcc_forallElim_code "` no encuentra nada. Solo existen `pcc_forallElim_code'` (ForallElimCodePrf:173) y `_open` (:85).
- Texto: `pcc_forallElim_code` pasa a `` `pcc_forallElim_code'` `` en los dos sitios.

**4a‑09** · `TrackedAtomsPrf.lean:651` · NOTA.
- Evidencia: `DEUDA_hGuardT`/`DEUDA_hGuardF` están en LineWFGuardPrf:208/211 y `DEUDA_chainOkBDot` en D3ChainDotPrf:134. Este último lo descarga `DEUDA_chainOkBDot_of_hbody` (:990), dentro de la cadena `d3_prf_real` → `d3_prf_of_halves`.
- El kit se usa en código en HasWitTracked, HasWitFTracked, D3ChainDot (:241, :518) y PremsBdAll (:989, :1287).
- Texto: «✏️ 2026‑10‑14 (ADR‑134): hoy existen los tres y están descargados: `DEUDA_hGuardT`/`DEUDA_hGuardF` (`Meta/LineWFGuardPrf.lean`) por `pcc_hGuardT` y `pcc_hGuardF`, y `DEUDA_chainOkBDot` (`Meta/D3ChainDotPrf.lean`) dentro de `d3_prf_real` (`Meta/PremsBdAllPrf.lean`), vía `d3_prf_of_halves` y `DEUDA_chainOkBDot_of_hbody`. El kit lo usan `HasWitTrackedPrf` y `HasWitFTrackedPrf` (C3), y `D3ChainDotPrf` y `PremsBdAllPrf` (D3).»

**4a‑10** · `TrackedAtomsPrf.lean:26` · CORREGIDO (puntero).
- Evidencia: `prf_In_iff_boundedIn` está en BoundedInPrf:379, no en :391.
- Texto: «(`Meta/BoundedInPrf.lean`)».

**4a‑11** · `TrackedCorePrf.lean:51` y `:107` · NOTA.
- Evidencia: `GODEL-D3-TRACKED-DESIGN.md` §11.2 y :1827, y el commit `e08a1e2`. `repr_pos'_prfₜ` y `hI_tracked` nunca se declararon: en los `.lean` solo aparecen en comentarios.
- `prf_tc_form` se retiró en `6f66e61` (ADR‑012, 2026‑08‑18).
- La infraestructura se usa en código, por ejemplo D3ChainDotPrf:338 y :385, y BdAllIntroPrf:148.
- Texto en :51: «✏️ 2026‑10‑14 (ADR‑134): registro — el plan D1ₜ no se ejecutó: el enfoque `tcFn` de raíz se descartó en la sesión 2026‑07‑05c (`GODEL-D3-TRACKED-DESIGN.md` §11.2, commit `e08a1e2`), y ni `repr_pos'_prfₜ` ni `hI_tracked` llegaron a declararse; `prf_tc_form` se retiró con `ax_tc_cons` (ADR‑012, 2026‑08‑18). D3 se probó por la vía punteada: `d3_prf_real` (`Meta/PremsBdAllPrf.lean`). La infraestructura de este módulo sí se usa (`liftFormula_provFromCode_open`, `substFormula_provFromCode_open`, `atom2CodeFn`, `prf_congr_atom2CodeFn`; entre otros, en `Meta/D3ChainDotPrf.lean`). Lo que sigue describe el estado del 2026‑07‑05b.»
- Texto en :107: «(✏️ 2026‑10‑14, ADR‑134: D1ₜ no llegó a existir —ver la nota de la cabecera—; `atom2CodeFn` y su congruencia los usa la vía punteada.)»

**4a‑12 y 4a‑13 (cabecera)** · `ReflectionPrf.lean:47` · NOTA.
- Evidencia: `Meta/Reflection.lean` se borró en `b1dedd1` (ADR‑115). `d3_prf` solo existió en un documento de diseño.
- Medido: ninguna de las cinco exportaciones se usa fuera del módulo, salvo `d3_prf_of_sigma1` en Sigma1BoundedPrf:99. `hI_refutable` está en `sondeos/D3Sigma1Vacuo.lean`.
- Texto: «⛔ ✏️ 2026‑10‑14 (ADR‑134): registro — `Meta/Reflection.lean` se borró con la capa `⊢` (ADR‑115), y `d3_prf` nunca fue una declaración: la D3 probada es `d3_prf_real` (`Meta/PremsBdAllPrf.lean`), por la vía punteada (`d3_prf_of_halves`, `Meta/D3ChainDotPrf.lean`), sin usar nada de este módulo. Y el «núcleo duro» no está por probar: `hI` es REFUTABLE (ADR‑132, T05: `hI_refutable` en `sondeos/D3Sigma1Vacuo.lean`, compilado el 2026‑10‑12), así que `d3_prf_of_sigma1` es cierto y VACUO.»

**4a‑13 (docstring)** · `ReflectionPrf.lean:87` · NOTA.
- Texto: «⛔ **VACUO** (✏️ 2026‑10‑14, ADR‑134; ADR‑132, T05): `hI` es refutable —`hI_refutable`, `sondeos/D3Sigma1Vacuo.lean`—, así que este teorema no reduce D3 a nada; el D3 que se usa es `d3_prf_real` (`Meta/PremsBdAllPrf.lean`), por la vía punteada.»

**4a‑14** · `Sigma1Prf.lean:41` · NOTA.
- Texto: «✏️ 2026‑10‑14 (ADR‑134): registro — ese cierre no puede existir para `hI`: es REFUTABLE (ADR‑132, T05: `hI_refutable` en `sondeos/D3Sigma1Vacuo.lean`, compilado el 2026‑10‑12), y con ella `d3_prf_of_sigma1` es VACUO. D3 se probó por otra vía, la punteada: `d3_prf_real` (`Meta/PremsBdAllPrf.lean`).»

**4a‑15** · `Sigma1AtomPrf.lean:353` · NOTA.
- Evidencia: la nota del obstáculo es de `0aa85a0` (2026‑07‑10, 13:31) y `ax_lineWF_inv` entró en `3a30197` (13:42).
- `prf_lineWF_inv` (:369) usa `ax_lineWF_inv ∈ axioms`, y `pcc_lineWF_tracked` tiene exactamente esa fórmula.
- Texto: «(✏️ 2026‑10‑14, ADR‑134: once minutos después, el mismo 2026‑07‑10, `ax_lineWF_inv` entró en la lista —su cierre es `prf_lineWF_inv`, abajo—, y la fórmula de arriba ES hoy un teorema sin hipótesis: `pcc_lineWF_tracked` (`Meta/SubstTreeReflect.lean`), C3, cerrado el 2026‑09‑10. Sigue siendo cierto que este lema es el transporte, no la producción.)»

**4a‑16** · `Sigma1AtomPrf.lean:187` · NOTA.
- Evidencia: `prf_lineWF_leibniz (concl A t1 t2) (hwA …) (hwt1 …) (hwt2 …)` en ReprPrf:848. El texto es del 2026‑07‑10, anterior a ADR‑020.
- Texto: «(✏️ 2026‑10‑14, ADR‑134: desde ADR‑020 los códigos ya no son arbitrarios: `prf_lineWF_leibniz` (`Meta/ReprPrf.lean`) pide las guardas `hwA : Prf (hasWitF A)`, `hwt1 : Prf (hasWit t1)` y `hwt2 : Prf (hasWit t2)`, y el `⇔` de arriba vale bajo ellas; ver la corrección del 2026‑09‑05 en `pcc_leibniz_code`.)»

**4a‑17** · `Sigma1AtomPrf.lean:43` · NOTA. Una sola nota en la cabecera cubre :28, :36, :90 y :239.
- Evidencia: `hbI_refutable`. Los usos citados están en SubstTreeReflect:1150 y :1158, y en HasWitFTrackedPrf:60.
- Texto: «✏️ 2026‑10‑14 (ADR‑134): registro — la ruta `hbI`/`hbC` a la que servía este módulo, y con ella la «fase 5» que anuncian esta cabecera, `prf_provCodeC'_eq_of_tracked` y la sección de la igualdad con `tcFn`, es VACUA: `hbI` es refutable (ADR‑132, T05: `hbI_refutable` en `sondeos/D3Sigma1Vacuo.lean`), así que `d3_prf_of_reflect_bounded` no reduce D3 a nada. D3 se probó por la vía punteada (`d3_prf_real`, `Meta/PremsBdAllPrf.lean`). Las piezas sí se usan: `eqCodeFn` y `lineWFCodeFn` están en C3 (`pcc_lineWF_tracked`, `Meta/SubstTreeReflect.lean`), y `prf_lineWF_inv` lo usa `pcc_tag_vacuous`.»

**4a‑18** · `Sigma1BoundedPrf.lean:44` (cabecera, cubre :25 y :32‑42) y `:91` (docstring) · NOTA.
- Evidencia: el fichero se creó en `18e2b10` (2026‑07‑09). Solo lo importa `Meta.lean:81`. `hbI_refutable` usa `prf_hI_of_reflect_boundedIn`.
- Texto en :44: «⛔ ✏️ 2026‑10‑14 (ADR‑134): registro — esta reducción es VACUA (ADR‑132, T05): `hbI` es refutable (`hbI_refutable` en `sondeos/D3Sigma1Vacuo.lean`, compilado el 2026‑10‑12, que la lleva a `hI_refutable` con `prf_hI_of_reflect_boundedIn` de aquí), así que ninguna instancia de las hipótesis de `d3_prf_of_reflect_bounded` existe y las fases 3‑5 de esta ruta no tienen objetivo. Ningún módulo de producción consume este (sólo lo importa el barril `Meta.lean`). El D3 que se usa es `d3_prf_real` (`Meta/PremsBdAllPrf.lean`), por la vía punteada. Lo que sigue describe el plan del 2026‑07‑09.»
- Texto en :91: «⛔ **VACUO** (✏️ 2026‑10‑14, ADR‑134; ADR‑132, T05): `hbI` es refutable —`hbI_refutable`, `sondeos/D3Sigma1Vacuo.lean`—, así que este teorema no reduce D3 a nada; el D3 que se usa es `d3_prf_real` (`Meta/PremsBdAllPrf.lean`; el `d3_prf` de arriba nunca fue una declaración), por la vía punteada.»

**4a‑19** · `Sigma1CorePrf.lean:56` (cabecera, cubre :36‑41 y :52) y `:148` · NOTA.
- Evidencia: `inFormCodeFn` se usa en TrackedAtoms, HasWitTracked y HasWitFTracked.
- Texto en :56: «✏️ 2026‑10‑14 (ADR‑134): registro — `hI` no tiene un «obstáculo» técnico que salvar: es REFUTABLE con el modelo `MNV V₀` (ADR‑132, T05: `hI_refutable` en `sondeos/D3Sigma1Vacuo.lean`, compilado el 2026‑10‑12), y ese cierre inductivo no existe. D3 se probó por la vía punteada (`d3_prf_real`, `Meta/PremsBdAllPrf.lean`). El constructor `inFormCodeFn` sí se usa: lo usa C3 (`Meta/TrackedAtomsPrf.lean`, `Meta/HasWitTrackedPrf.lean`, `Meta/HasWitFTrackedPrf.lean`).»
- Texto en :148: «(✏️ 2026‑10‑14, ADR‑134: este caso vale y está probado abajo; la `hI` general a la que apuntaba es refutable: ver la nota de la cabecera.)»

**4a‑20 y 4a‑21** · `Sigma1TrackedPrf.lean:58` · NOTA. Una nota en la cabecera cubre :38‑42, :52 y :53‑56.
- Evidencia: ADR‑012 dice «`axioms ⊢ ⊥`, verificado en el compilador», y EvalListPrf:82 lo confirma. `pcc_dot_cons` está en DotConsPrf:335. §11.2 y `e08a1e2` como en 4a‑11.
- Texto: «✏️ 2026‑10‑14 (ADR‑134): registro — la Opción A de raíz (`provFormulaC'ₜ`/D1ₜ) se descartó en la sesión 2026‑07‑05c (`GODEL-D3-TRACKED-DESIGN.md` §11.2, commit `e08a1e2`), y ni `hI_tracked` ni `repr_pos'_prfₜ` llegaron a declararse. `prf_tc_cons` ya no existe: era consecuencia de `ax_tc_cons`, que hacía inconsistente la teoría y se retiró con ADR‑012 (2026‑08‑18); su sustituto, dentro de `Prov`, es `pcc_dot_cons` (`Meta/DotConsPrf.lean`). D3 se probó por la vía punteada (`d3_prf_real`, `Meta/PremsBdAllPrf.lean`). Lo de abajo, el puente para testigos CERRADOS, sigue siendo correcto.»

## NUEVAS (dos punteros, corregidos sin nota)

- `HasWitTrackedPrf.lean:412`: decía `sondeos/A3IsFCBTracked.lean:205`, pero `PsiF` está en :208. Ahora dice «`sondeos/A3IsFCBTracked.lean` define su `PsiF`».
- `TrackedAtomsPrf.lean:193`: decía `…A3IsFCBTracked.lean:318`, pero `bdInB` está en :321. Ahora dice «(idiom de `bdInB` en `sondeos/A3IsFCBTracked.lean`)».

## Ficheros tocados (`git diff --stat`) y marcadores

| Fichero | Cambios | `/-` antes → después | `-/` antes → después |
|---|---|---|---|
| HasWitFTrackedPrf | 10 (+9 −1) | 64 → 64 | 64 → 64 |
| HasWitTcFnPrf | 4 (+2 −2) | 29 → 29 | 29 → 29 |
| HasWitTrackedPrf | 25 (+19 −6) | 91 → 91 | 91 → 91 |
| ReflectionPrf | 12 (+11 −1) | 10 → 10 | 10 → 10 |
| Sigma1AtomPrf | 19 (+17 −2) | 43 → 43 | 43 → 43 |
| Sigma1BoundedPrf | 14 (+13 −1) | 5 → 5 | 5 → 5 |
| Sigma1CorePrf | 9 (+8 −1) | 29 → 29 | 29 → 29 |
| Sigma1Prf | 5 (+5) | 24 → 24 | 24 → 24 |
| Sigma1TrackedPrf | 7 (+7) | 5 → 5 | 5 → 5 |
| TrackedAtomsPrf | 16 (+12 −4) | 34 → 34 | 34 → 34 |
| TrackedCorePrf | 12 (+11 −1) | 19 → 19 | 19 → 19 |

En total, 114 inserciones y 19 borrados. Las 19 líneas borradas son todas texto de comentario. Los acentos graves de las líneas nuevas están emparejados, ninguna fecha ni ADR lleva guion ASCII y no aparece `prf_axiomsCodeT_eq`.

## Punteros de otros ficheros que mis líneas nuevas desplazan

No son de mi lista; los dejo para ti:
- `HilbertDeduction.lean:62`: `HasWitTrackedPrf:757` → ahora :761. `HasWitFTrackedPrf:183` sigue valiendo.
- `sondeos/D3Sigma1Vacuo.lean:14/16`: `ReflectionPrf.lean:80-82` → ahora :90‑92, y `Sigma1BoundedPrf.lean:83-87` → ahora :95‑99. Lo mismo en `doc/AUDITORIA-SUELO-2026-10-12.md:302‑303`, pero es un registro fechado.
- `LiftcCodePrf.lean:56`: `Sigma1AtomPrf.lean:122` (`eqCodeFn_eq_eqc`) → ahora :129.

Estos otros ya estaban desfasados antes de mis cambios:
- `Sigma1AtomPrf.lean:246`, citado en EvalSubsttcPrf:741, CHANGELOG, NEXT-STEPS, REFERENCE-Incompleteness y `sondeos/EvalSubsttc`. Hoy esa línea es `pcc_eq_tracked`, en :271.
- `Sigma1CorePrf:114/188/204/213/218/268`, citados en docs y sondeos.

La línea base de los recuentos está en `<tmp>/scratchpad/suelo/comentarios/grupo-4a-baseline.txt`.

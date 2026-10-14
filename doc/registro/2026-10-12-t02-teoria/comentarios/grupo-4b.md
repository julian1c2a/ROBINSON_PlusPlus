# Grupo 4b · las guardas de ADR‑020 y lo demás

**Last updated:** 2026-10-14 — registro (ADR‑134): copia tal cual de lo que se produjo ese día; no se actualiza. La marca está para el control `[E]` de `check-doc-sync.bash`, que mira todo `.md` versionado.

Ficheros (sólo éstos), en `ROBINSON_PlusPlus/Meta/`: `ForallElimCodePrf.lean`, `PropCodePrf.lean`,
`ExIntroCodePrf.lean`, `Div2ParityPrf.lean`, `ListEtaPrf.lean`, `MpCodePrf.lean`, `ReprPrf.lean`,
`Representability2.lean`, `RunFnBoundedPrf.lean`, `InAxiomsCodePrf.lean`.

Contexto: ADR‑020 (`DECISIONS.md`, grep «^## ADR-020») metió las guardas DENTRO de los esquemas de sustitución; los
lemas `prf_lineWF_*` que el comentario describe «para códigos arbitrarios» piden guardas (`hwA`, `hwt`, `hwF`, `hwT`,
`hwa`…). Mira la firma en `ReprPrf.lean` y escribe la que es. C3 CERRADO el 2026‑09‑10 y D3 PROBADA el mismo día; la
capa `⊢` (con `d3`) retirada con ADR‑115.

Prioridad: A = falso hoy y relevante; M = media; D = dudoso; m = menor.

- 4b‑01 · `ForallElimCodePrf.lean:39‑40` · `prf_lineWF_q1` «arbitrarios» · pide `hwA` y `hwt` (ReprPrf ≈ :785). **A**
- 4b‑02 · `ForallElimCodePrf.lean:80‑82` · «Sólo pide `Ac` cerrado» · `_open` pide `hwF`/`hwT`. **A**
- 4b‑03 · `PropCodePrf.lean:120‑121` y `:27‑29` · `prf_lineWF_ind` «código `a` arbitrario» · pide `hwa`
  (ReprPrf ≈ :871). **A**
- 4b‑04 · `ExIntroCodePrf.lean:31` · «el ensamblaje queda planificado abajo» · Está hecho: `pcc_exIntro_code'`
  (≈ :79). **A**
- 4b‑05 · `ExIntroCodePrf.lean:75‑78` · «(`hAc`, `hw`)… en `d3`» · la firma pide `hwF`/`hwT` (no `hw`), y `d3` no
  existe (era el de ⊢; D3 hoy es `d3_prf_real`). **A**
- 4b‑06 · `Div2ParityPrf.lean:116` · «Lo consumen L2 y… L3» · L3 no lo usa (lo dice el propio :185). **m**
- 4b‑07 · `Div2ParityPrf.lean:29‑31` · lo da por pendiente y está cerrado (compruébalo). **D**
- 4b‑08 · `ListEtaPrf.lean:197` · «Consumidor previsto» · ya lo consume PremsOfTagPrf (≈ :106). **M**
- 4b‑09 · `MpCodePrf.lean:305‑306` · punteros (compruébalos; mejor por símbolo). **m**
- 4b‑10 · `ReprPrf.lean:272` · «tres longitudes» · falta la 2 (`thy`; compruébalo). **m**
- 4b‑11 · `Representability2.lean:42‑45` y los encabezados vacíos :90, :93, :96 y :115 · anuncian el tracking y D1,
  pero el fichero sólo tiene el encoder y dos guardas; todo lo demás está en Representability2Prf. **A**
- 4b‑12 · `RunFnBoundedPrf.lean:24‑30` · «SONDEO… Hipótesis a contrastar» · es producción y la hipótesis está probada
  (≈ :57). **D**
- 4b‑13 · `InAxiomsCodePrf.lean:62`, `:76` y `:216` · `prf_tc_form` · no existe; el propio fichero dice «murió» en
  ≈ :236. Hoy es `pcc_tc_formCode_internal` (compruébalo). **A**

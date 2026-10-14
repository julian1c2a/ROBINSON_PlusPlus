# Grupo 4a · los testigos rastreados, la reflexión Σ₁ y la vacuidad de `hI`/`hbI`

**Last updated:** 2026-10-14 — registro (ADR‑134): copia tal cual de lo que se produjo ese día; no se actualiza. La marca está para el control `[E]` de `check-doc-sync.bash`, que mira todo `.md` versionado.

Ficheros (sólo éstos), en `ROBINSON_PlusPlus/Meta/`: `HasWitFTrackedPrf.lean`, `HasWitTrackedPrf.lean`,
`HasWitTcFnPrf.lean`, `TrackedAtomsPrf.lean`, `TrackedCorePrf.lean`, `ReflectionPrf.lean`, `Sigma1Prf.lean`,
`Sigma1AtomPrf.lean`, `Sigma1CorePrf.lean`, `Sigma1BoundedPrf.lean`, `Sigma1TrackedPrf.lean`.

Contexto: C3 CERRADO el 2026‑09‑10 (`pcc_lineWF_tracked`, SIN HIPÓTESIS). La deuda «B6b» está pagada (`PrfH_mono`,
`PrfH_w1`, `Meta/HilbertDeduction.lean:76/96`; compruébalo). **La vacuidad (ADR‑132, T05)**: `hI : ∀ x L, Prf (In x L
⇒ provCodeC' (In x L))` es REFUTABLE (`sondeos/D3Sigma1Vacuo.lean`, compilado el 2026‑10‑12: con `x := #0`,
`L := cons zero nil` y las valoraciones 0 y 1, contra la solidez en `MNV V₀`), y `hbI` cae con ella. Por eso
`d3_prf_of_sigma1` (`ReflectionPrf.lean:80`) y `d3_prf_of_reflect_bounded` (`Sigma1BoundedPrf.lean:83`) son ciertos y
VACUOS: ninguna instancia de sus hipótesis existe. No se retiran en este commit: se MARCAN en sus docstrings y en las
cabeceras que los presentan como reducción con contenido. Forma sugerida: «⛔ VACUO (ADR‑132, T05): `hI` es
refutable —`sondeos/D3Sigma1Vacuo.lean`—, así que este teorema no reduce D3 a nada; el D3 que se usa es
`d3_prf_real`, por la vía punteada.» El «obstáculo» de `hI` no es técnico: es falsa.

Prioridad: A = falso hoy y relevante; M = media; D = dudoso; m = menor.

- 4a‑01 · `HasWitFTrackedPrf.lean:182‑183` · B6b dada por abierta; `PrfH_mono` existe. **A**
- 4a‑02 · `HasWitFTrackedPrf.lean:1192‑1203` · «NO deja `pcc_lineWF_tracked` incondicional… hay 14… Nada lo consume» ·
  Es incondicional, y `pcc_hGuardF` se usa en SubstTreeReflect (≈ :779, :813, :848). **A**
- 4a‑03 · `HasWitTrackedPrf.lean:606‑607` · «lo único que queda» · Lo descargan §8 y §9. **D**
- 4a‑04 · `HasWitTrackedPrf.lean:757` · B6b. **A**
- 4a‑05 · `HasWitTrackedPrf.lean:1261‑1266` · «Nada lo consume» · Lo usan HasWitFTracked y SubstTreeReflect
  (`pcc_hGuardT`); `DEUDA_wfAll1_tracked` está probada (≈ :904). **A**
- 4a‑06 · `HasWitTrackedPrf.lean:20‑21` y `:987` · punteros a Axioms caducados (el verificador: hoy :1241 y :1244):
  mejor por símbolo. **m**
- 4a‑07 · `HasWitTrackedPrf.lean:24` y `TrackedAtomsPrf.lean:31` (T10) · dicen en presente que
  `sondeos/A3IsFCBTracked.lean` «probó» algo; hoy no compila (rc 1, su :355; `sondeos/pasadas/tabla_adr129.txt`). Nota
  de procedencia: «(✏️ …: el sondeo es hoy registro: no compila desde …)». No borres la cita. **M**
- 4a‑08 · `HasWitTcFnPrf.lean:19` y `:411` · `pcc_forallElim_code` no existe (hay `'` y `_open`; compruébalo). **m**
- 4a‑09 · `TrackedAtomsPrf.lean:643‑647` · «C3 (`DEUDA_hGuardT/F`) y D3 (`DEUDA_chainOkBDot`), ninguno de los cuales
  existe todavía» · Existen los tres, y el kit lo usan HasWitTracked, HasWitFTracked y D3ChainDot. **A**
- 4a‑10 · `TrackedAtomsPrf.lean:26` · puntero. **m**
- 4a‑11 · `TrackedCorePrf.lean:35‑49` y `:97` · Plan D1ₜ (`repr_pos'_prfₜ`) · ese nombre no existe y el plan se
  descartó el 2026‑07‑09 (compruébalo con git log/grep); :46 cita `prf_tc_form`, que no existe. **M**
- 4a‑12 · `ReflectionPrf.lean:34‑36` · cita `Meta/Reflection.lean` y `d3_prf`, que no existen. **A**
- 4a‑13 · `ReflectionPrf.lean:41‑45`, `:73‑79` y el docstring de `d3_prf_of_sigma1` (:80‑82, T05) · «núcleo duro
  claramente especificado» · `hI` es refutable: VACUO. **A**
- 4a‑14 · `Sigma1Prf.lean:28‑39` · «necesita aún la inducción object» para `hI` · `hI` es refutable y D3 se cerró por
  la vía punteada. **A**
- 4a‑15 · `Sigma1AtomPrf.lean:337‑341` · «sin axioma de inversión… no es derivable» · `ax_lineWF_inv` está en la lista,
  `prf_lineWF_inv` está 13 líneas más abajo, y la fórmula es `pcc_lineWF_tracked` (compruébalo). **A**
- 4a‑16 · `Sigma1AtomPrf.lean:171‑177` · «códigos arbitrarios» · faltan las guardas de ADR‑020 (mira la firma). **A**
- 4a‑17 · `Sigma1AtomPrf.lean:28`, `:36`, `:90` y `:239` · remiten a la ruta `hbI`, que es vacua. **M**
- 4a‑18 · `Sigma1BoundedPrf.lean:25`, `:32‑42` y `:76‑87` (T05) · presentan como reducción lo que es vacuo. **A**
- 4a‑19 · `Sigma1CorePrf.lean:36‑41`, `:52` y `:137` · «El obstáculo de `hI`…» · `hI` es refutable: no hay obstáculo
  técnico que salvar. **A**
- 4a‑20 · `Sigma1TrackedPrf.lean:52` · `prf_tc_cons` «sí computa» · No existe. **A**
- 4a‑21 · `Sigma1TrackedPrf.lean:38‑42` y `:53‑56` · «requiere la Opción A de raíz» · La Opción A se descartó;
  `hI_tracked` no existe (compruébalo). **M**

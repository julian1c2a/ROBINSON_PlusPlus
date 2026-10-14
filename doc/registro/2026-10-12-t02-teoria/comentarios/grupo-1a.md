# Grupo 1a · la raíz, los barriles, Minimal, Full y los titulares de Gödel

**Last updated:** 2026-10-14 — registro (ADR‑134): copia tal cual de lo que se produjo ese día; no se actualiza. La marca está para el control `[E]` de `check-doc-sync.bash`, que mira todo `.md` versionado.

Ficheros (sólo éstos; rutas desde la raíz de RPP): `ROBINSON_PlusPlus.lean`, `ROBINSON_PlusPlus/Meta.lean`,
`ROBINSON_PlusPlus/Full/Induction.lean`, `ROBINSON_PlusPlus/Minimal/Axioms.lean`, y en `ROBINSON_PlusPlus/Meta/`:
`Consistencia.lean`, `GodelTwo.lean`, `GodelTwoPrf.lean`, `DiagonalNumeral.lean`, `DiagonalTwo.lean`,
`Provability.lean`, `HilbertSeq.lean`, `HilbertDeduction.lean`, `DerivCondPrf.lean`.

Prioridad: A = falso hoy y relevante; M = media; D = dudoso; m = menor.

## Raíz y barriles
- 1a‑01 · `ROBINSON_PlusPlus.lean:13` · «Meta: Gödelización (Nivel B codificación + Nivel C demostrabilidad). Ver
  GODEL-STATUS.md» · Falta todo el Nivel D, y GODEL-STATUS.md se declara histórico (su l.74). → p. ej. «-- Meta:
  codificación, `Prf`, D1–D3, el modelo de los 142, `consistencia`, Gödel I/II sin hipótesis y Tarski (estado vivo:
  NEXT-STEPS.md).» **M**
- 1a‑02 · `ROBINSON_PlusPlus.lean:18` y `Full/Induction.lean:35‑37` · «La inducción de la cadena es el constructor
  `Prf.ind`» · También entra `Prf.listInd`: D2, D3 y Gödel II lo usan (AXIOMS.md §0.3). → «…los constructores
  `Prf.ind` y `Prf.listInd`.» **M**
- 1a‑03 · `Full/Induction.lean:47` (T31) · dice «23 primitivos» y el código prueba 24 (compruébalo: `primAxioms`).
- 1a‑04 · `Full/Induction.lean:71‑73` · llama «`Full`» a lo que hoy es `Prf`; y `:232` es el esquema de `Prf.ind`,
  no un axioma. Matiz menor: nota si hace falta. **m**
- 1a‑05 · `Meta.lean:8‑17` · La API pública no nombra `consistencia`, `goedel_I`, `goedel_II`, `goedel_I_neg`,
  `godelCN_indecidible` ni `tarski`, aunque los importa. Junto con :20‑21 sugiere que ⊬¬G no existe. → añadir
  «· Sin hipótesis: `consistencia`, `goedel_I`, `goedel_II` (Consistencia); `goedel_I_neg`, `godelCN_indecidible`
  (SolidezVerificador); `tarski`, `tarski_semantico` (TarskiPrf).» **A**
- 1a‑06 · `Meta.lean:17` · «La consistencia de los 142… (`consistencia`)» · DUDOSO: `ConsistentH` es la consistencia
  de `T_Prf` (los 142 con los esquemas de `Prf`), no la de la lista. **D**
- 1a‑07 · `Meta.lean:20‑21` · está marcado, pero la nota debe decir que la mitad `⊬¬G` VOLVIÓ, sobre `Prf`, con
  ADR‑121 (`goedel_I_neg`), si no lo dice ya. **M**

## Minimal/Axioms.lean
- 1a‑10 · `:108‑109` · «π₁(x,y) = \frac{\frac{(x+y)(x+y+1)}{2}+y}{2}» · Divide dos veces. El código es
  `pair = div2 (cantor_poly) = ((x+y)(x+y+1)+2y)/2` (≈ :115‑134; :119 lo dice bien); el π₂ no corresponde a nada. →
  la fórmula de Cantor correcta, `π(x,y) = (x+y)(x+y+1)/2 + y` (= `cantor_func`; compruébalo en el código), y quitar
  o corregir el π₂. Error de contenido matemático: (B), con «(✏️ 2026‑10‑14: decía …)». **A**
- 1a‑11 · `:52‑55`, `:87‑88`, `:334‑335`, `:353` y `:1679‑1680` · «ahora son defs concretas en Block4_C6_C7…
  `proj_is_cantor`» / «Son necesarios para las pruebas de C5» · Nada de eso existe (compruébalo con grep). Sus vecinas
  :1676, :1681 y :1692 sí llevan «(retirado, ADR‑115)». **M**
- 1a‑12 · `:343‑344` · lo de la inducción es cierto, pero dice «(sorry pendiente)»: no hay ningún `sorry` pendiente,
  y su gemela :1681 ya pone «(sorry; retirado, ADR‑115)». **M**
- 1a‑13 · `:577` · «etiquetas de regla 0..17» · Son 0..20. **A**
- 1a‑14 · `:893` y `:898` · «Sus 3 ecuaciones» / «la única pieza que falta para la diagonalización» · En la lista hay
  2 (compruébalo); la diagonal está hecha (`prf_ancla`, ADR‑117). **M**
- 1a‑15 · `:170` · «línea ~441 / ~833» · punteros caducados (el verificador dice que hoy son :472 y :918): mejor por
  símbolo. **m**

## Meta/
- 1a‑20 · `Consistencia.lean:49` · «🏁 **Los 142 son CONSISTENTES**: `Prf ⊥` no tiene prueba» · identifica
  `ConsistentH` con la consistencia de la lista. → p. ej. «🏁 **`T_Prf` es CONSISTENTE** (los 142 con los esquemas de
  `Prf`): `MNV V₀` es estándar y satisface los 142 (`estandar_MN`), y `Prf` es sólido en él.» **A**
- 1a‑21 · `GodelTwo.lean:45‑47` · «hoy su única hipótesis es `ConsistentH`» · Existe `goedel_II` sin hipótesis
  (`Consistencia.lean:57`). **A**
- 1a‑22 · `GodelTwo.lean:114‑117` (T31) · «la consistencia de los 142 axiomas sigue sin probar»: el verificador lo da
  por marcado (HISTÓRICO‑MARCADO); la auditoría (T31) por falso. Mira si la marca existente basta; si no, nota. **M**
- 1a‑23 · `GodelTwoPrf.lean:200‑205` · «con `ConsistentH` desaparecen… los dos esquemas de inducción» · Desaparecen los
  dos `axiom`, no la inducción: Gödel II usa `ind` y `listInd` como constructores de `Prf` (AXIOMS.md §0.3). **M**
- 1a‑24 · `DiagonalNumeral.lean:52‑54` · «hoy, sólo con `ConsistentH`» · calla que `ConsistentH` es teorema y que
  existe `goedel_I`. **D**
- 1a‑25 · `DiagonalTwo.lean:93‑95` · dice que ⊬¬G «no tiene hoy formulación sobre `Prf`»: FALSO desde ADR‑121. →
  «(✏️ 2026‑10‑14, ADR‑134: hoy sí la tiene, `goedel_I_neg`, por la solidez del verificador en `MNV V₀`; Rosser,
  ⊬R ∧ ⊬¬R sólo con `ConsistentH`, sigue ⬜.)» **A**
- 1a‑26 · `DiagonalTwo.lean:52‑53` y `:89` · «Gödel I es `goedel_first_prf`» · Hoy Gödel I va entero y sin hipótesis:
  `goedel_I` + `goedel_I_neg` (`godelCN_indecidible`). **A**
- 1a‑27 · `Provability.lean:23` · «NIVEL C: DEMOSTRABILIDAD (provisional, en construcción)» · Hoy el fichero sólo es
  la codificación (compruébalo). **M**
- 1a‑28 · `Provability.lean:223‑224` · «Hoy Gödel I es `goedel_first_prf`» · Es `godelCN_indecidible`, sin
  hipótesis. **M**
- 1a‑29 · `HilbertSeq.lean:411` · «el objeto `demFormula`» · No existe; es `provFormulaC'` (compruébalo). **A**
- 1a‑30 · `HilbertSeq.lean:407`, `:449` y `:458` · «Reemplaza el postulado…» · Esos postulados se retiraron en F7a
  (compruébalo en DECISIONS/NEXT-STEPS con grep «F7a»). **D**
- 1a‑31 · `HilbertDeduction.lean:26‑27` · la lista de constructores omite `listInd`. **M**
- 1a‑32 · `HilbertDeduction.lean:95` · «el caso que consumen los cuatro módulos» · `PrfH_w1` no lo usa nadie
  (compruébalo con grep en todo el árbol). **A**
- 1a‑33 · `HilbertDeduction.lean:168` · `provCodeC'_elim` no es una declaración (compruébalo). **m**
- 1a‑34 · `DerivCondPrf.lean:26` · «Porte de `Meta/DerivCond.lean`» · Ese módulo se retiró y este fichero no lleva
  banner. → «(D2 sobre ⊢; retirado, ADR‑115)». **M**

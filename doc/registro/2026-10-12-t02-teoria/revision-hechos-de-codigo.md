# Revisión adversarial de T02 · hechos de código

**Last updated:** 2026-10-14 — registro (ADR‑134): copia tal cual de lo que se produjo ese día; no se actualiza. La marca está para el control `[E]` de `check-doc-sync.bash`, que mira todo `.md` versionado.

> Registro: el informe final de un agente de sólo lectura, tal cual (fecha: 2026-10-14). Lo que dice del árbol es de esa fecha; lo aplicado, en ADR-134.

Revisé el índice (`git diff --cached`, 28 ficheros). La salida `induccion_1014.txt` cuadra con la tabla de §0.3 fila a fila; los fallos están en el texto que la resume. No ejecuté nada. Los números de línea son del árbol de trabajo.

## Hallazgos

**1. FALSO.** `sondeos/README.md:111`: «Fuera de las traducciones…, sólo construyen pasos dos reglas derivadas, `prf_nat_induction` y `prf_list_induction`».
- **Problema:** la fila pregunta también por `qconf`, y aquí queda la versión anterior a la corrección de `deduction_aux`. Tampoco cuenta las `linea_*` de `goedel_I_neg`.
- **Evidencia:**
  - `HilbertDeduction.lean:134` construye `PrfH.qconf Γ A C`.
  - `ChainPrf.lean:531, 582, 638, 715` construyen `Prf.qconf`.
  - `induccion_1014.txt:10` y `:15` (D3: 26 lemas en 7 módulos).
  - `SolidezVerificador.lean:456-469`.
- **Arreglo:** «…sólo dos reglas derivadas construyen pasos `ind`/`listInd`; `qconf` lo construyen el caso `gen` de `deduction_aux` y lemas de siete módulos; en `goedel_I_neg`, las `linea_*`».

**2. FALSO.** `sondeos/README.md:111`: «(`prf_zero_or_succ`, `prf_add_zero_left`…: hechos que Q no demuestra)».
- **Problema:** `prf_zero_or_succ` es Q3, un axioma de Q. Además `AXIOMS.md:121-125` y `:178-179` dicen que la lista prueba los dos sin inducción.
- **Arreglo:** «…hechos que la lista prueba sin inducción y aquí se probaron por inducción».

**3. INCOHERENTE.** `sondeos/InduccionTitulares.lean:32-34` frente a `:48-50`.
- **Problema:**
  - Las líneas 32-34 dicen que `linea_ind`, `linea_listInd`, `linea_p3` y `linea_qconf` CONSTRUYEN pasos. Es cierto: `linea_p3` hace `exact Prf.p3 _` (`SolidezVerificador.lean:456-457`).
  - Las líneas 48-50 dicen «ningún titular construye un paso `p3`» y presentan `linea_p3` como algo que solo lo «nombra». Pero `goedel_I_neg` es titular y `linea_p3` está en su frontera (`induccion_1014.txt:54`).
  - Además, la línea 32 («lo que CONSTRUYE pasos son dos reglas derivadas») choca con las 36-38, que dicen que `qconf` también se construye.
- **Arreglo:** usar el mismo verbo en todo el docstring (o «construye» o «traduce desde el modelo») y poner la excepción de `goedel_I_neg` en la línea 48.

**4. INEXACTO.** `AXIOMS.md:179-180`: «ningún titular construye un paso clásico: sus derivaciones sólo llevan los `p3` que traducen de otra que reciben».
- **Problema:** en `goedel_I_neg`, los `p3` salen de decodificar una cadena que el MODELO acepta (`ev_provCodeC'` → `verificador_solido` → `linea_p3`), no de traducir una derivación recibida como argumento.
- **Lo mismo, sin la excepción:** `NEXT-STEPS.md:16`, `DECISIONS.md:3` y `sondeos/README.md:3` y `:111`. Solo ADR‑134 §3 (`DECISIONS.md:10189-10190`) y la fila de la tabla la recogen.
- **Arreglo:** añadir «salvo `goedel_I_neg`, que decodifica con `linea_p3` las líneas aceptadas en el modelo».

**5. INCOHERENTE.** `README.md:148`: «**0 `axiom` de Lean** en todo el árbol».
- **Problema:** contradice §0.2, que declara canónica (`AXIOMS.md:144-146`): hay cuatro en `sondeos/`. La línea no se tocó, pero está junto a las viñetas tocadas.
- **Evidencia:** `sondeos/PilotoDiagonal.lean:34, 38` y `sondeos/lintlab/Uso.lean:29, 31`.
- **Arreglo:** «0 en el build; 4 en `sondeos/`, fuera del build (AXIOMS.md §0.2)».

**6. INEXACTO.** `AXIOMS.md:115`: «los 22 `ax_vpf_*`…, que ninguna prueba nombra: T68».
- **Problema:** los nombra la validación del modelo, y T68 lo dice así.
- **Evidencia:** `ModeloCodificacion.lean:151-190` (`v_vpf_*`); `doc/AUDITORIA-SUELO-2026-10-12.md:891` («sólo los nombra la validación del modelo»).
- **Arreglo:** «que sólo nombra la validación del modelo».

**7. INEXACTO.** `AXIOMS.md:132-133`: «(el modelo lo rellena con 0, por elección)».
- **Problema:** el modelo decide por la etiqueta, no siempre 0:
  - `substtcN` con etiqueta 0/1 y otra forma calcula un resultado (`ModeloCodigo.lean:253-260`).
  - `premsOfN` con etiqueta 16/17 da un `consN` sea cual sea la longitud (`:512-515`).
  - `vpfN` decodifica cualquier número (`:491`).
  - Solo da 0 en nil, en la resta truncada y en etiquetas desconocidas.
- **Arreglo:** «el modelo elige un valor: 0, o el que da su análisis por la etiqueta».

**8. INEXACTO.** `AXIOMS.md:149` y `DECISIONS.md:10168-10169`: «`::` los de siempre».
- **Problema:** `Estandar` fija `::` = `consN`, el σ del par de Cantor (ADR‑113); no hay un cons «de siempre» en ℕ. Además, ADR‑134 §2 omite «y los 142 verdaderos» (`haxs`).
- **Evidencia:** `SolidezPrf.lean:95-99`.
- **Arreglo:** «`::` = `consN` (σ del par de Cantor) y los 142 verdaderos».

**9. INEXACTO.** `AXIOMS.md:332`: «`Prf.ind` vale para toda fórmula, y es PA».
- **Problema:** §0 dice «contiene a PA», y deja abierta la conservatividad (`:120`, `:128`).
- **Arreglo:** «y contiene a PA».

**10. INEXACTO.** `Minimal/Axioms.lean:1584-1585` (y `DECISIONS.md:10218`): «`premsOf`, sólo sobre las líneas que cumplen `lineWF`».
- **Problema:** las ecuaciones `ax_premsOf_*` fijan `premsOf` sobre la forma literal (etiqueta y longitud), cumpla la línea `lineWF` o no; no dependen de `lineWF`.
- **Evidencia:** `Axioms.lean:1393-1395` y `:1440-1441`.
- **Arreglo:** «sólo sobre las líneas con la forma de su regla».

**11. OMISIÓN.** `AXIOMS.md:134`: «(es lo esperable, porque `t < h :: t`, por inducción fuerte)».
- **Problema:** falta la otra mitad: que todo L ≠ nil es un h :: t (la sobreyección de Cantor). En el árbol, `prf_nil_or_cons_all` se prueba precisamente con `listInd` (`induccion_1014.txt:209`).
- **Evidencia:** `descompone` en `SolidezPrf.lean:62-71`.
- **Arreglo:** añadir «y que todo L ≠ nil es un h :: t».

**12. INEXACTO (cronología).** `AXIOMS.md:128-130` y `DECISIONS.md:10164`: «ADR‑054 §4 la descartó… cuando `ax_tc_cons`… la hacía falsa».
- **Problema:** ADR‑054 es posterior a ADR‑012, que ya había retirado `ax_tc_cons`. ADR‑054 lo cita en pasado («vivía»).
- **Evidencia:** `DECISIONS.md:4246` y `:495`.
- **Arreglo:** «la descartó como metateorema general: `ax_tc_cons` (retirado en ADR‑012) había dado `axioms ⊢ ⊥`».

**13. INEXACTO.** `InduccionTitulares.lean:38`: «también lo construyen varios lemas de `ChainPrf`».
- **Problema:** se queda corto. En D3 y Gödel II son 26 lemas en 7 módulos; solo en D2 son 4, todos de `ChainPrf`.
- **Evidencia:** `induccion_1014.txt:15, 20, 30, 50` frente a `:10`.

**14. OMISIÓN.** `Meta/HilbertSeq.lean:160`: la cabecera sigue diciendo «Solidez del verificador: `Proves rs φ → Prf φ`».
- **Problema:** la nota nueva de `:42` dice que esos nombres no existen. Además, «esos tres nombres» es ambiguo: la lista de arriba tiene cuatro y `checkProof` sí existe.
- **Arreglo:** nombrarlos explícitamente y cambiar la cabecera a `Derivation rs φ → Prf φ`.

**15. FORMA.** `AXIOMS.md:176-177`: «"No", que ninguna constante de su cierre lo construye».
- **Problema:** tomado al pie de la letra es falso: `stepConcl_prf` (`HilbertSeq.lean:201`) y `deduction_aux` (`HilbertDeduction.lean:122-125`) construyen el paso al traducirlo.
- **Arreglo:** «…fuera de las traducciones y de `deduction_aux`».

**16. FORMA.** `AXIOMS.md:145-146`: «…y dos en `lintlab/Uso.lean`, que prueban que un linter los detecta».
- **Problema:** la oración relativa solo vale para `lintlab`. Los dos de `PilotoDiagonal` son lo que el piloto asumía de S4 (`PilotoDiagonal.lean:31-38`).

**17. OMISIÓN.** Tabla de `AXIOMS.md:165-172`.
- **Problema:** mide `prf_tarski`, la forma sintáctica. Los titulares sin hipótesis son `tarski` y `tarski_semantico` (`TarskiPrf.lean:94, 131`). Para `tarski` el resultado sale por unión con `consistencia`, pero no se dice.

**18. OMISIÓN.** `Meta/NatArithPrf.lean:36-37` cita `NatMulPrf.lean:95-96`.
- **Problema:** `NatMulPrf.lean:95-96` dice «se probó antes de disponer de `ax6_add_comm`», y es falso: `ax6` está en la lista desde `9757405` (2026‑05‑10) y `NatArithPrf` es de `2d7c17c` (2026‑07‑07). Esa frase de `NatMulPrf` no se corrigió.

**19. FORMA (M‑13).** `InduccionTitulares.lean:31` y `AXIOMS.md:159-160` fechan la medida el 2026‑10‑12.
- **Problema:** la ejecución archivada es del 2026‑10‑14, y el párrafo de `qconf` se reescribió después.
- **Arreglo:** añadir «re‑ejecutado el 2026‑10‑14, mismo resultado».

**20. FORMA (aviso).** `sondeos/InduccionTitulares.lean` tiene 37 líneas sin añadir al índice (`esSemantica`, `cierreSin`, `#modelo`, de T09).
- **Problema:** el docstring no las menciona, y la salida no las ejecuta. Si se vuelve a hacer `git add` antes del commit de T02, entrarán sin describir.

**21. OMISIÓN.** El inventario de ADR‑134 §5 no recoge cuatro cambios hechos:
- la nota de `Proves` en `HilbertSeq.lean:42`;
- la corrección de `ax21` a «PRIMITIVO» (`Axioms.lean:1676`);
- la nota de `README.md:132`;
- la frase de entrada de `README.md:93-94`.

## Comprobado y correcto

**Punto 1 (AXIOMS.md §0):**
- Los constructores: los 17 de `Prfᵢ` y los 7 de `Prf` (`Hilbert.lean:94-160`), y las fórmulas `inductionFormula` y `listInductionFormula`.
- Los 33 símbolos: 28 de función y 5 de relación, cada uno con una sola aridad. `nil` es `zero`, y `le` y los dos símbolos que sobran (`nil_sym`, `le_sym`) no se usan; coincide con `MNV`.
- `ax2`, `ax3`, `ax4`, `ax5`, `ax8` y `ax9` son los seis axiomas de Peano. Q3 sale de `ax2`, `ax5`, `ax13` y `ax19`; `0 + n = n` sale de `ax6` con `ax4`, y `σm + n = σ(m + n)` de `ax6` con `ax5`.
- Las cifras 34, 107 y 142 (`axioms_len`, `axioms_split`); los 22 `ax_vpf_*`; `ax21` como primitivo.
- `prf_sound`: `ind` por inducción en ℕ, `listInd` por `descompone` y `fuerte`, `p3` por `byContradiction`.
- Solo hay solidez de `Prfᵢ` respecto de todo modelo, en `AnclaSoundness`, que compila.
- La cuenta de `axiom`: 0 en el build de RPP y de FOL, 15 en `cuarentena/` de FOL, 4 en `sondeos/`; `leanchecker` corre en la CI.
- No hay ningún puente con `DerivesSet₀`.
- Cada fila de la tabla de §0.3 frente a la salida: los «sí» tienen la regla derivada en la frontera y un camino por valores; los «no» solo tienen traducciones o análisis por casos.

**Punto 2 (docstring del sondeo frente al fuente):** las cuatro traducciones (`prfH_nil_to_prf`, `prf_to_prfH`, `stepConcl_prf`, `prf_to_derivation`) reconstruyen cada paso con el constructor homónimo sin añadir ninguno.
- **Construyen:** `prf_nat_induction` y `prf_list_induction` son la regla y dos MP.
- **Traducen o analizan por casos:**
  - `deduction_aux` traduce `ind`, `listInd` y `p3`, y construye `qconf` en el caso `gen`.
  - `prf_chainOk_track` analiza por casos: en `ind` y `listInd` usa los axiomas `lineWF_*`, sin `Prf.ind`.
  - `stepConcl_shift`, `lineJustif.match_1` y los `casesOn` son análisis por casos.
- El método es sólido: BFS en `#camino`, recorrido por tipos y valores.

**Punto 3:** el párrafo de `T_Prf` en el README, la viñeta de `⊬¬G` (`goedel_I_neg`), la de «Hay prueba de consistencia», y las cifras de 2 y 107 módulos. ADR‑134 §2 y §3 cuadran con la salida (camino de 18 aristas a `prf_add_zero_left`, los 9 usuarios de `ChainPrf`), salvo lo señalado en 8, 10 y 12.

**Punto 4:** los comentarios corregidos de los nueve `.lean` son ciertos, salvo los puntos 10 y 14. Las notas sobre `ConsistentH` y `T_Prf`, `thy` sobre `axioms`, `ax_tc_cons` retirado en ADR‑012, `axiomsCodeT` en tres de los 142, y `Prfᵢ` sin confinamiento ni inducción están bien. **Ningún comentario quedó mal cerrado:** todos los `-/` y `/-` añadidos sustituyen a delimitadores que se quitaron.

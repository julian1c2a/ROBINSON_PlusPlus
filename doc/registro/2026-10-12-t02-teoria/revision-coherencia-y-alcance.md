# Revisión adversarial de T02 · coherencia y alcance

**Last updated:** 2026-10-14 — registro (ADR‑134): copia tal cual de lo que se produjo ese día; no se actualiza. La marca está para el control `[E]` de `check-doc-sync.bash`, que mira todo `.md` versionado.

> Registro: el informe final de un agente de sólo lectura, tal cual (fecha: 2026-10-14). Lo que dice del árbol es de esa fecha; lo aplicado, en ADR-134.

Revisé el diff entero (28 ficheros, 634+/72−) contra el árbol, en sólo lectura. Hay 2 frases falsas y unos 20 hallazgos más. Ninguno rompe el build: en los `.lean` sólo cambian comentarios.

## Hallazgos

**FALSO**

1. **`sondeos/README.md:111`**: «D1 usa la inducción (`prf_zero_or_succ`, `prf_add_zero_left`…: hechos que Q no demuestra)».
   - **Problema:** `prf_zero_or_succ` es `n = 0 ∨ ∃k n = σk`, que es el Q3 de Robinson, un **axioma de Q** (lo lista la tabla de `MINIMAL-AXIOMS.md` §1.1). Además, `AXIOMS.md:178-180` dice que los dos primeros salen de la lista sin inducción.
   - **Arreglo:** «hechos que la lista demuestra sin inducción (`ax6`+`ax4`; Q3 de `ax2`, `ax5`, `ax13`, `ax19`) y que aquí se probaron por inducción».

2. **`sondeos/README.md:111`**: «Fuera de las traducciones… sólo construyen pasos dos reglas derivadas, `prf_nat_induction` y `prf_list_induction`».
   - **Problema:** la fila pregunta también por `qconf`. El propio sondeo (`InduccionTitulares.lean:36-38`) dice que `deduction_aux` y otros lemas construyen pasos `qconf`, y que `linea_*` construye pasos en `goedel_I_neg`.
   - Además, el sondeo dice «varios lemas de `ChainPrf`» (l.38) y se queda corto: `Prf.qconf` se construye directamente en `ChainOkBoundedPrf` (l.285, 309, 577, 598, 641…), `SubstfcWitnessPrf`, `CodeWitnessPrf`, `HasWitTcFnPrf`, `EvalLiftcPrf`, `EvalNthcPrf` y `RunFnBoundedPrf`.
   - **Arreglo:** limitar la frase a `ind` y `listInd`, y decir quién construye `qconf`.

**Afirmar más de lo medido / INCOHERENTE**

3. **`AXIOMS.md:322-323`**: «el ENUNCIADO de D1 no la necesita».
   - **Problema:** contradice `AXIOMS.md:180` y ADR‑134 §3, que dicen «si D1 se puede probar sin ninguna, no está medido».
   - **Arreglo:** «por la teoría no debería necesitarla; en RPP, sin medir (§0.3)».

4. **`AXIOMS.md:120-123`** (y sus copias en `README.md:108`, `Hilbert.lean:152`, `Minimal/Axioms.lean:32`, GODEL-STATUS §1 y MINIMAL-AXIOMS): «contiene a PA (por lectura): los seis axiomas de Peano… y la inducción vale para toda fórmula».
   - **Problema:** la justificación omite que también hace falta que la lógica de `Prf` sea completa. Esa es justo la dirección `DerivesSet₀ → Prf`, y `AXIOMS.md:136-137` dice que no existe ningún puente; T67 lo registra como MEDIDO («con solidez pero sin completitud lógica»). Lo mismo vale para «la lista sola ya contiene a Q».
   - **Arreglo:** «tiene los axiomas de PA y su esquema de inducción completo; que contenga a PA pide además la completitud de su lógica (un Hilbert estándar; en el árbol, sin probar: T67)».

5. **`AXIOMS.md:168, 169, 171`**: las atribuciones «(por D1)», «(por D2)» y «(por el punto fijo)».
   - **Problema:** `#camino` da *un* camino más corto, no la única entrada. `goedel_first_prf` usa a la vez `repr_pos'_prf` y `prf_godelCN_fixedpoint` (`GodelTwoPrf.lean:212-217`). `goedel_I_neg` usa el punto fijo y también `Consistencia.goedel_I`, que pasa por D1 (`SolidezVerificador.lean:558-570`). `prf_con_imp_godel` usa `d2_prf` y `d3_prf_real` (`GodelTwoPrf.lean:163-185`).
   - **Arreglo:** «p. ej., por D1», o nombrar las dos entradas.

6. **`AXIOMS.md:283-305`**: la nota dice «una frase es FALSA y dos inexactas», pero deja sin marcar otras del mismo texto.
   - **Problema:** sigue sin marca el «Hecho clásico: Q no satisface las condiciones HBL… no prueba (D3)» y «para D2/D3 hace falta inducción», cuando la propia nota dice de D3 en Q «que falle, no está publicado». También pone a «el propio Q» como ejemplo de que D1–D3 no son necesarias.
   - Además, `AXIOMS.md:18` («la inducción… es el mínimo teórico de Gödel II (Q no satisface D2/D3)») y `AXIOMS.md:272` («son el mínimo teórico de Gödel II») siguen afirmando lo que la nota llama falso.
   - **Arreglo:** marcar :18, :272 y la frase de D2/D3.

7. **`NEXT-STEPS.md:3699-3710`**: «dos frases de esta nota son falsas».
   - **Problema:** la nota siguiente acaba con «`Minimal` es la teoría OBJETO que se aritmetiza, `Full` es donde vive la prueba» (l.3709), que es justo lo que ADR‑134 corrige; y dice «hace falta IΣ₁/EA» (l.3704), cuando AXIOMS §1.1 dice que basta S¹₂.
   - Además, en `NEXT-STEPS.md:4509` la nota corrige «rastrea IΣ₁» pero deja, en la misma viñeta, «(honesto: Prf modela IΣ₁)».

8. **El sondeo dice dos cosas distintas de las líneas del verificador.**
   - `InduccionTitulares.lean:32-34` cuenta `linea_ind/listInd/p3/qconf` entre lo que «CONSTRUYE pasos». En cambio, l.48-50 dice «ningún titular construye un paso `p3`… (y `linea_p3`)», y `AXIOMS.md:171` y `DECISIONS.md:10189-10191` lo llaman traducción.
   - Además, la lista «NO la alcanzan» de `listInd` (l.46-47) omite `goedel_I_neg`, que `AXIOMS.md:171` sí da por no alcanzado.
   - **Arreglo:** usar una sola palabra («traduce») y añadir `goedel_I_neg` a la lista.

**INEXACTO**

9. **`AXIOMS.md:159-161, 175-176`**: «Medido… por cierre de dependencias» y «"No", que ninguna constante de su cierre lo construye».
   - Lo automático sólo separa las 4 traducciones; el resto (`deduction_aux`, `prf_chainOk_track`, `stepConcl_shift`, los `match`) se clasificó leyendo el fuente. ADR §3 lo dice; AXIOMS no.
   - Además, las traducciones del cierre sí construyen esos pasos (`HilbertDeduction.lean:85-99`, `HilbertSeq.lean:198, 385`).
   - **Arreglo:** «medido, y el resto clasificado por lectura»; «"No": ninguna construye un paso nuevo».

10. **`AXIOMS.md:142-143`**: «sus tres axiomas… son el footprint de los titulares (`check-footprints.bash`)».
    - D2 tiene `[propext, Quot.sound]`, sin `choice` (`AUDITORIA:810`). D1, D2 y `prf_con_imp_godel` no tienen fila en `check-footprints` (T11b).

11. **`AXIOMS.md:332`**: «y es PA».
    - Contradice «contiene a PA» y «no se sabe si es conservativa sobre PA» (§0.1).
    - **Arreglo:** «su inducción es la de PA».

12. **`PLAN-SORTES.md:17`**: «lo ERA, por `ax_tc_cons`…; desde ADR‑120 es consistente».
    - La fila habla de `axioms ⊢ ⊥`. Después de ADR‑012, `⊢` seguía siendo refutable (`ax_list_induction` daba `⊥`, L1‑2; las meta‑reglas también) y se retiró en ADR‑115. `consistencia` es la de `Prf`, otro cálculo.
    - En la misma línea, `CodeNumeralPrf.lean:32` dice «la inconsistencia que TUVO», en singular; hubo otra: `Prf ⊥` con el `cons` viejo, reparada en ADR‑113.

13. **`AXIOMS.md:129-130` y `DECISIONS.md:10164`**: «ADR‑054 §4 la descartó cuando `ax_tc_cons`… la hacía falsa».
    - ADR‑054 es del 2026‑09‑17, posterior a ADR‑012 (2026‑08‑18), y su §4 (`DECISIONS.md:4247`) dice «`ax_tc_cons` *vivía*». Descartó un metateorema general con un contraejemplo que ya era pasado.

14. **Notas que llaman «Q» a la lista.**
    - `ESCALANDO_EL_PROYECTO.md:50` llama «la LISTA» a «Robinson Q (34 axiomas)», y `GODEL-D-ARITHMETIZATION.md:54` deja «Q (= axiomas de Minimal)». Pero la lista no es Q (§0.1; MINIMAL‑AXIOMS: ni siquiera es conservativa sobre Q).
    - En ese mismo fichero ya tocado, `ESCALANDO:81-83` sigue diciendo que el puente es `prf_to_derives`, que no existe (se retiró en ADR‑115) y que §0.1 niega.

15. **`Minimal/Axioms.lean:30-31`**: «142 axiomas… sobre 33 símbolos», en una cabecera que dice definir el lenguaje.
    - El módulo define 35 símbolos: `nil_sym` («[]») y `le_sym` («≤») no los nombra ningún axioma, porque `nil := zero` y `le := lt ∨ eq`. AXIOMS §0.1 lo dice bien.

16. **Detalles menores.**
    - `AXIOMS.md:420`: `goedel_first_real'` se retiró con ADR‑012, no con la capa `⊢`.
    - `GODEL-STATUS.md:74`: «FALSO desde ADR‑121» se queda corto; «5 `axiom`» y `goedel_second'` eran falsos ya desde ADR‑115.
    - `DECISIONS.md:10241-10242`: «la de AXIOMS.md lleva una nota fechada»; la de GODEL‑STATUS también.

17. **`DECISIONS.md:10129`**: «(el commit, el 2026-10-13)».
    - Es una quinta fecha de commit escrita a mano, aparte de las cuatro marcas que ya conocéis. Hoy es 2026‑10‑14.

**OMISIÓN**

18. **`DECISIONS.md:10229-10230`**: «180 apariciones (22 FALSO‑VIGENTE, 46 sin marca)».
    - No hay artefacto en el árbol: «FALSO‑VIGENTE» sólo aparece en DECISIONS y no hay carpeta de ADR‑134 en `doc/registro/`. Tampoco se da el id del workflow (ADR‑114 sí lo da, l.8407).
    - El reparto cubre 68 de 180 y no dice cuántas se corrigieron. Va contra T00 y M‑13.

19. **`AXIOMS.md:159-172`**: la tabla no tiene columna `qconf` y no explica por qué, aunque la frase anterior la nombra y promete «cada regla».

20. **El Ámbito de ADR‑134** omite `DEPENDENCIES.md` y `doc/AUDITORIA-SUELO…` (25 listados + DECISIONS + esos 2 = 28).
    - Por si no lo teníais: `README.md:148` («0 `axiom`… en todo el árbol») contradice §0.2.

**FORMA**

21. **`NEXT-STEPS.md:3699-3702`**: la nota no lleva una línea `>` en blanco, así que se funde en un solo párrafo con la «Nota foundacional» que corrige.
22. **`doc/REFERENCE-Kernel.md:10-14`**: la nota parte la frase «esquemas del verificador … estructural».
23. **`AXIOMS.md:300`**: cita «IΣ₁ (o EA)», pero el texto (l.287) dice «(o EA/IΔ₀+exp)». Además, Hájek–Pudlák aparece como III.2.17 y III.2.22 en AXIOMS y sólo como III.2.17 en ADR §4.
24. **`AUDITORIA-SUELO`:**
    - El «Estado» de T25/T28 (l.440, 482) va antes de *Grupo*, al revés que en T02/T03/T00.
    - Las referencias README:101/103/108/139 son de la numeración anterior: tras el commit, :108 cae en el párrafo de `T_Prf`.
    - Los «Estado» van fechados el 2026‑10‑12 y la marca del documento dice 2026‑10‑13.

## Comprobado y bien
- **Cifras:**
  - Ficheros: 28.
  - Sondeos: 92 de primer nivel (91 en HEAD); 39 que compilan = 35 + 4.
  - Módulos: Meta 107 + Minimal 2 + Full 3 = 112.
  - Axiomas: 142 = 34 + 107 + el ancla, y hay 22 `ax_vpf_*`.
  - Símbolos: 33 = 28 de función + 5 de relación.
  - Cuarentena de FOL: 15 `axiom` en `.lean`.
- **Contenido:**
  - Los seis de Peano (`ax2`, `ax3`, `ax4`, `ax5`, `ax8`, `ax9`) y `ax6`, `ax7`, `ax10`–`ax12` están bien nombrados.
  - Las derivaciones sin inducción (Q3, `0+n`, `σm+n`) se sostienen por lectura.
  - `axiomsCodeT` aparece exactamente en 3 de los 142.
  - El modelo rellena la basura con 0.
  - `Estandar` tiene los 4 campos que se le atribuyen.
  - `ax_L0_cons_def` es `σ(pair)`, y la tabla de REFERENCE-Kernel tiene 34 filas.
  - `Prf.p3` sólo se construye en traducciones y en `linea_p3`.
  - `prf_runFn_concat` más otros 8 de `ChainPrf` usan `prf_list_induction`.
  - `Derives0.lean:107-108` y la cadena `TarskiPrf → Lift0 → Derives0` son correctos.
- **Declaraciones:**
  - Existen todos los identificadores del texto nuevo, incluidos `Derivation`, `prf_iff_derivation`, `DerivesSet₀`, `model_existence_iff₀`, `funcc`, `listFormCodeM`, `lineJustif` y `linea_*`.
  - Los nombres retirados van marcados como tales.
- **Forma:**
  - En los `.lean` no hay `/-` ni `-/` sueltos; el sondeo tiene 10 aperturas y 10 cierres; los cambios son sólo comentarios.
  - Ninguna fila de tabla editada cambia su número de columnas.
  - Las comillas «» están equilibradas.
- **Alcance y controles:**
  - Todos los documentos tocados sin marca subida están en `E_DEUDA`.
  - No se ha tocado `doc/book/**` ni `PLAN-LIBRO.md`.

# Informe para decidir T01 (Rosser)

**Last updated:** 2026-10-14 — registro (ADR‑134): copia tal cual de lo que se produjo ese día; no se actualiza. La marca está para el control `[E]` de `check-doc-sync.bash`, que mira todo `.md` versionado.

> Registro: el informe final de un agente de sólo lectura, tal cual (fecha: 2026-10-14). Lo que dice del árbol es de esa fecha; lo aplicado, en ADR-134.

# Informe para T01: cómo hacer el teorema de Rosser

**Ámbito.** Sólo he leído: no he compilado nada, no he tocado git y no he creado ficheros. Etiquetas:
- **MEDIDO**: leído o contado hoy en el árbol, o medido por el proyecto (cito dónde).
- **INFERIDO**: razonamiento sin compilar (digo de quién es).
- **ESTIMACIÓN**: esfuerzo no medido, con su fuente.

Las líneas son las del árbol de trabajo de hoy, que incluye ADR‑134. La auditoría cita las del 2026‑10‑12 y algunas se han movido: `axD` estaba en `Minimal/Axioms.lean:1099` y hoy está en `:1110`.

## Resumen

- **El problema.** Con la teoría T fija y `consistencia` demostrada, cualquier `rosser (hcon : ConsistentH)` equivale en Lean a su conclusión sin hipótesis. Esa conclusión ya sale por la solidez en unas decenas de líneas, y ningún control lo distinguiría. El contenido «basta la consistencia simple» sólo puede vivir en dos sitios: en el enunciado (opción a) o en un certificado sobre la prueba (opción b, con el control T08).
- **Las cuatro opciones, en una línea cada una:**
  - **(a‑i)** pone el contenido en el enunciado sin tocar T, V₀, G ni los 107 axiomas de codificación. A cambio, la familia es autoanclada (no es «T+E») y hay que parametrizar `Prf` («semanas», ESTIMACIÓN).
  - **(a‑ii)** es la más cercana al libro y la más cara: reabre el verificador y el modelo, con un coste sin medir.
  - **(b)** deja el enunciado trivial y pone el contenido en T08. Su NegNum es la más cara.
  - **(c)** no cuesta nada, y pierde el argumento, NegNum, PosNum y el corolario de ω‑incompletitud.
- **Ninguna da el Rosser de los libros** («toda T r.e. ⊇ Q, consistente»). Todas heredan los esquemas fijos de `Prf` y, con listas de axiomas, sólo cubren extensiones finitas.

## 0. Lo que fija el problema (MEDIDO)

- **`Prf` no tiene parámetro de teoría.**
  - La regla de axiomas es `thy (a) : List.Mem a axioms → Prfᵢ a` (`Meta/Hilbert.lean:110`).
  - `axioms` son los 141 de la base más el ancla (`Minimal/Axioms.lean:1641`, `:1646`, `:1791`).
  - `p3`, `ind`, `qconf` y `listInd` son constructores para toda fórmula (`Hilbert.lean:153-160`). Por lectura, T_Prf contiene a PA (ADR‑134 §2, `DECISIONS.md:10155-10160`).
- **La teoría entra en el verificador objeto por un solo sitio**, la regla `thy`: `In (carc x) axiomsCodeT` (`Axioms.lean:1415-1418`).
  - `axiomsCodeT` es una constante opaca (`:1075`).
  - El axioma diagonal `axD axiomsBase` la fija al código de los 142 (`:1096-1111`, `:1646`; ADR‑117 §2).
  - Por eso `provFormulaC'` (`Meta/ProofChain.lean:107-108`), `godelCN` y `consistencyFormula'` hablan de esa teoría y sólo de ella.
- **`consistencia : ConsistentH` es un teorema** (`Meta/Consistencia.lean:50`), por el modelo `MNV V₀` y `prf_sound` (`Meta/SolidezPrf.lean:145`, `:193`).

## 1. Por qué `rosser (hcon : ConsistentH) : ¬Prf R ∧ ¬Prf ¬R` sería trivial hoy

1. **El tipo no puede llevar la información.** `ConsistentH := ¬ Prf ⊥` (`Hilbert.lean:173`) es un teorema. Para toda P, `(ConsistentH → P) ↔ P`: en un sentido se aplica `consistencia`, en el otro basta `fun _ => p`. Una prueba de la versión con hipótesis no se distingue de una sin ella. Es lógica inmediata y la auditoría lo dice así (`doc/AUDITORIA-SUELO-2026-10-12.md:1009`). El verificador de T01 añade que vale también por la ruta P (`doc/registro/2026-10-12-auditoria-suelo/workflow-cierre.json`, `verifs[0]`, T01).
2. **La conclusión es barata sin Rosser.** Basta el patrón de `goedel_I_neg` (`Meta/SolidezVerificador.lean:558-569`; 12 líneas de código, MEDIDO por la crítica del plan): la solidez en `MNV V₀`, W1 (`prf_of_prov`, `:540`) y `consistencia`. Para R (INFERIDO):
   - Si `Prf R`, el modelo cree en una prueba y, por R, en una prueba de ¬R; W1 da `Prf ¬R`, luego `Prf ⊥`.
   - Si `Prf ¬R`, el modelo cree en una prueba de R; W1 da `Prf R`, luego `Prf ⊥`.
   - El plan lo cotiza en 60–120 líneas (ESTIMACIÓN, `doc/registro/2026-10-05-adr122-d7-rosser/resultado.json:218`).
   - Con cualquier sentencia en lugar de R, `godelCN_indecidible` (`:572-574`) ya lo da sin escribir nada.
3. **La Etapa 0 ya hecha va por la ruta que mete el modelo.**
   - `sondeos/RosserReflexion.lean` llama a `prf_sound estandar_MN` en las líneas 130, 145, 156 y 162. También usa W1, cuya rama `thy` reescribe con `V₀_eq_codigo` (`SolidezVerificador.lean:458-463`), y éste se prueba con `prf_sound` (`Consistencia.lean:62-68`).
   - Un Rosser montado así tendría en su cierre la solidez de T, de la que `ConsistentH` sale sola: `hcon` sería decorativo también en la prueba (FUN‑01 y RUT‑01 del registro; crítica, `resultado.json:292`, §ROSSER 1.1).
   - `sondeos/RosserBasura.lean` §1–§4 no usa el modelo: `prf_sound` sólo aparece en el control §5 (`:204-205`).
4. **Nada lo distinguiría hoy.**
   - Los titulares de los dos sondeos dan `[propext, Classical.choice, Quot.sound]` (`RosserReflexion.lean:45`; `RosserBasura.lean:47-48`), igual que `goedel_first_prf` (consistencia simple) y que `goedel_I_neg` (solidez).
   - Ningún `check-*.bash` recorre el cierre transitivo (T08, AUDITORIA:258).
   - El control negativo al estilo de Tarski (`example (hbot : Prf ⊥) …`, `Meta/TarskiPrf.lean:121-123`) es vacuo con T fija, porque su hipótesis es refutable.

**Conclusión.** «Trivial» se refiere al enunciado, no a la prueba de libro, que sigue costando lo que cueste NegNum. El contenido sólo cabe en un enunciado cuantificado sobre teorías donde la hipótesis pueda fallar, o en un certificado sobre el término de prueba (AUDITORIA:144, :1015 e). Hoy no hay ningún Rosser en el build: en los `.lean`, `NegNum`, `PosNum` y `rosser_de` sólo aparecen en la prosa de `RosserReflexion`, y `PrfL`, `axiomsOf` y `ConsistentL` no aparecen en ninguno (MEDIDO, grep).

## 2. Las opciones

**Piezas comunes a todo Rosser sintáctico, (a) y (b):**
- **El esqueleto** (Etapa 7 del plan, `resultado.json:274`): ρ(x) := ∀y (Pf(y,x) → ∃z ≤ y Pf(z,⌜¬x⌝)) y R := `selfAppN (diagBeta ρ)`, con `prf_diagonal`, que ya es general (`TarskiPrf.lean:49`).
  - La mitad ⊬R usa PosNum, NegNum y `prf_bdAll_numeral` (`CodeWitnessPrf.lean:866`).
  - La mitad ⊬¬R usa `prf_lt_trichotomy` (`NatMulPrf.lean:291`).
  - INFERIDO: Rosser no necesita D2 ni D3.
- **Lo que falta.**
  - NegNum: refutar en la teoría que un numeral que no es prueba lo sea. Incluye GuardNeg, la refutación hereditaria de las guardas `hasWit`/`hasWitF`; las guardas son Σ₁, de modo que lo que hay que demostrar es su negación, Π₁. También faltan 8 de las 11 proyecciones `lineWF ⇒ guarda` (hay 3), la refutación de `thy` sobre numerales y NegChain.
  - PosNum: no hay ningún lema `proofCode' … =eq numeral` (`resultado.json:206`).
- **Etapa 0 (MEDIDO):** dos de sus tres piezas.
  - `RosserReflexion` (ruta H), 189 líneas.
  - `RosserBasura` (neutral), 217 líneas.
  - Juntas, 406 líneas de fichero y 194 de declaraciones (ADR‑126 §2, `DECISIONS.md:9699-9701`).
  - Faltan la hereditaria general, `hasWitF` sobre numerales y la línea `q1` basura (`NEXT-STEPS.md:37-38`).
  - Las dos compilan en la pasada de ADR‑129 (`sondeos/pasadas/tabla_adr129.txt`), fuera de la CI.
- **Obligaciones que fija la auditoría:**
  - `IsSentence R`, como `liar_isSentence` (`TarskiPrf.lean:111`; T12).
  - R y ρ en `EV_TOK` (`check-sorry.bash:333`), con autotest.
  - Ninguna `simp`, `rfl` ni `decide` sobre ⌜R⌝ ni sobre el ancla: lemas ∀ y `rw`.
  - M‑14 (cotizar contra la firma y un consumidor), aún sin escribir (`NEXT-STEPS.md:756`).
  - Unidad de líneas: `strip-lean.awk`.
  - Los sondeos de Rosser en la CI (T06) y el contrato del enunciado (T07).

### (a‑i) Familia autoanclada

**(i) Enunciado** (Lean aproximado; nada de esto existe):
```lean
inductive PrfL (Γ : List Formula) : Formula → Prop          -- Prf con thy : a ∈ Γ → …
def axiomsOf (E : List Formula) := (axiomsBase ++ E) ++ [axD (axiomsBase ++ E)]  -- axiomsOf [] = axioms
theorem rosser_autoanclado (E : List Formula) (hE : ∀ φ ∈ E, IsSentence φ)
    (hcon : ¬ PrfL (axiomsOf E) ⊥) :
    ¬ PrfL (axiomsOf E) R ∧ ¬ PrfL (axiomsOf E) (neg R)     -- R: la MISMA fórmula para toda E
-- controles (CRI‑02, INFERIDOS): ¬PrfL (axiomsOf [neg consistencyFormula']) ⊥;
--   PrfL (axiomsOf [godelCN]) ⊥ y PrfL (axiomsOf [consistencyFormula']) ⊥
```
En matemáticas: sea B la base (los 141 con los esquemas). Para toda lista finita E de sentencias, sea T_E = B ∪ E ∪ {α_E}, donde α_E es el ancla diagonal sobre B ∪ E. Si T_E es consistente, T_E ⊬ R y T_E ⊬ ¬R, leyendo Pf con el ancla de T_E. La propia T es T_∅.

**(ii) Qué demuestra y qué no.**
- **Demuestra** un Rosser cuya hipótesis tiene contenido en el propio enunciado:
  - Es falsable: con E = [⊥] falla, y también con E = [godelCN], que es inconsistente (CRI‑02 (3), INFERIDO).
  - La familia incluye miembros consistentes y no sólidos, como T_{[¬Con']}. Su consistencia sale de `MNV V_E` más D1 para la nueva lista (CRI‑02 (2)); es ω‑inconsistente. Las dos cosas son INFERIDAS. En ese miembro la solidez no puede sustituir a la consistencia.
- **No demuestra nada sobre «T+E».** Para E ≠ [], T_E no contiene a T: dos anclas dan dos valores cerrados de `axiomsCodeT` y la base refuta su igualdad (CRI‑02 (c), INFERIDO). No expresa T+¬Con_T ni T+G_T, y la «T+Con'» de la familia es inconsistente.
- **¿Es el de los libros?** No. La forma de la hipótesis es la de Rosser, pero la clase de teorías es «extensiones finitas de la base, cada una con su ancla», todas con inducción completa.

**(iii) Qué hay que construir, qué existe y qué se reutiliza.**
- **Construir:**
  - `PrfL Γ`, y también `Prfᵢ` y `PrfH` con Γ (`PrfH` mete `Prfᵢ` por `incl0`, `HilbertDeduction.lean:41`), con `Prf` como instancia.
  - La monotonía en Γ.
  - `Estandar` con la lista como parámetro: hoy `haxs` mira `axioms` (`SolidezPrf.lean:99`), aunque el caso `thy` de la solidez ya es genérico (`:141`).
  - `v_ancla` para toda L: hoy sólo existe para V₀ (`ModeloCodificacion.lean:328`).
  - W1 paramétrico en V y en L; D1 para L; NegNum y PosNum para L.
- **Ya es genérico en L (MEDIDO):**
  - `axD`, `psiD`, `nD`, `deltaD` (`Axioms.lean:1096-1111`).
  - `prf_deltaD`, `prf_cola_axD`, `ancla_de_diagonal` (`Representability2Prf.lean:130`, `:141`, `:148`).
  - `MNV V` y la validación de los 141 para todo V (`ModeloEstandar.lean:12-14`, `:478`; `ModeloCodificacion.lean:339`).
  - `lineWFT V` y `chainOkN V` (`ModeloCodigo.lean:568`, `:604-608`).
- **Se reutiliza:** los dos sondeos de la Etapa 0, generalizados. La ruta H seguiría siendo admisible (INFERIDO, candidato FUN‑01 del registro): `MNV V_E` valida la base y α_E pero no E, así que el modelo sirve de oráculo sin descargar la hipótesis. Habría que comprobar que `pcc_eval_substfc_wit` y `pcc_eval_liftfc_wit` sólo usan la base y el ancla; no lo he leído.

**(iv) Coste.**
- **ESTIMACIÓN** (T62, AUDITORIA:856): el ADR, una tarde; el sondeo de viabilidad, 1–2 días; el refactor, «semanas». A eso se suma el Rosser por la ruta H: 1 400–2 250 líneas, sin unidad fijada y «probablemente optimista» según la crítica.
- **MEDIDO hoy** (grep textual con comentarios; es un radio, no un trabajo):

  | qué | líneas | ficheros |
  |---|---|---|
  | `Prf` | — | 105 de 113 |
  | `∈ axioms` | 333 | 41 |
  | `prf_ax` | 262 | 30 |
  | `PrfH` | 3 207 | 66 |
  | `axiomsCodeT` (sin comentarios) | 63 | 9 |

  Precedente de que el radio sobreestima: «163 módulos» fueron 3 ficheros (`doc/AUDITORIA-2026-09-18.md:882`).
- **La palanca probable** (INFERIDO): enunciar sobre `PrfL axiomsBase` todo lo que sólo usa la base y transportarlo por monotonía. Una prueba de `Prf` ya escrita no se puede transportar, porque T_E no contiene a T y el término no se inspecciona (AUDITORIA:1050).

**(v) Riesgos.**
- **CRI‑02 en pleno:** cada T_E habla de sí misma. El titular debe decir «extensiones finitas de la base, cada una con su ancla».
- **Vacuidad por diseño:** si la familia se restringe a E verdaderas en el modelo, la hipótesis vuelve a descargarse. Hace falta el control con ¬Con' y el control con ⊥.
- **Clases:** si se reintroducen, `#print axioms` no ve sus campos (MEDIDO con una sonda, `doc/AUDITORIA-FOL-2026-09-12.md` §6.2). Precedente: F1, donde una clase daba `Prf ⊥` (ADR‑117 §1).
- **El ancla:** la regla O1 («nada puede ejecutar `axioms`») se extiende a `axiomsOf`.

**(vi) Qué cambia en el resto del proyecto.**
- `axioms`, V₀, el ancla, `godelCN`, el verificador y los 107: nada. `godelCN` no depende de `axioms` (medido sobre el entorno, `doc/REFERENCE-Incompleteness.md:2162-2177`).
- `Prf` pasa a ser una instancia de `PrfL`.
- El modelo sólo se generaliza (`v_ancla`, `Estandar`, W1).
- Va con T62 y con la decisión de re‑certificar el censo 24+10 (T20).

### (a‑ii) Parámetro de teoría en `lineWF`/`chainOk`, o un segundo verificador

**(i) Enunciado** (Lean aproximado):
```lean
-- lineWF g x, chainOk g c p, con thy: In (carc x) g        (hoy: In (carc x) axiomsCodeT)
def Rsent (Γ : List Formula) : Formula := selfAppN (diagBeta (ρ Γ))   -- ρ con Prov de ⌜Γ⌝
theorem rosser_ext (E : List Formula) (hE : ∀ φ ∈ E, IsSentence φ)
    (hcon : ¬ PrfL (axioms ++ E) ⊥) :
    ¬ PrfL (axioms ++ E) (Rsent (axioms ++ E)) ∧ ¬ PrfL (axioms ++ E) (neg (Rsent (axioms ++ E)))
```
En matemáticas: si T+E es consistente (E finita), la sentencia de Rosser de T+E es indecidible en T+E.

**(ii) Qué demuestra y qué no.**
- **Demuestra** Rosser para toda extensión finita de T con su propio predicado de prueba. Incluye T+¬Con_T, cuya consistencia ya sale de `goedel_II` y `prf_deduction` en cuanto exista `PrfL` (AUDITORIA:850, INFERIDO inmediato), y T+G_T, y con ello la cadena de incurabilidad.
- **No demuestra** el caso de extensiones r.e. infinitas: haría falta dar los axiomas con una fórmula Σ₁, y nadie lo ha propuesto (INFERIDO).
- **¿Es el de los libros?** Es la opción más cercana.

**(iii) Qué hay que construir, qué existe y qué se reutiliza.**
- **Construir:** el verificador con parámetro (sus axiomas, su interpretación en el modelo y su validación), y además D1, el diagonal, W1, NegNum y PosNum sobre él. D2 y D3 sólo harían falta para Gödel II de las extensiones.
- **Existe:** `prf_diagonal`. A nivel de ℕ, el verificador ya es paramétrico en V, lo que abarataría el lado del modelo (INFERIDO).
- **Se reutiliza poco:** hay que portar la Etapa 0 al verificador nuevo.

**(iv) Coste.** «Sin medir» (AUDITORIA:55, :854); el refactor, «semanas» (ESTIMACIÓN). Cifras MEDIDAS hoy, textuales:
- De los 107 axiomas de codificación, 25 nombran `lineWF` o `chainOk`, y 2 nombran `axiomsCodeT` (`ax_lineWF_thy`, `ax_vpf_thy`).
- La maquinaria de D1 que habría que generalizar o duplicar: 634 líneas de `prf_lineWF_*` y 197 de `prf_chainOk_track` (`resultado.json:224`).

Por lectura, es la opción más cara (INFERIDO).

**(v) Riesgos.**
- Reabre el verificador y el modelo (`ModeloCodificacion`: 405 líneas, 48 s con carga; ADR‑120).
- Puede cambiar `axioms`, V₀ y el ancla.
- «Una segunda constante con su ancla no basta»: hace falta un verificador entero (verificador de CRI‑02, corrección e).
- La lección de F1 sigue en pie: un ancla que se contiene a sí misma no se puede postular (ADR‑117).

**(vi) Qué cambia en el resto del proyecto.** Los 25 axiomas (o 25 nuevos), su validación, D1 y `check-footprints`, y quizá `axioms`, V₀ y G. Es la opción de más radio.

### (b) NegNum por la ruta P, con T08 como criterio de aceptación

**(i) Enunciado** (Lean aproximado):
```lean
def NegNumStmt : Prop := ∀ (φ : Formula) (q : Nat),
  ¬ (chainOkN (codeNatList axioms) 0 q ∧ memN (codeNat φ) (runFnN 0 q)) →
    Prf (neg (Pf (numeralM q) (formCode φ)))
def PosNumStmt : Prop := ∀ φ, Prf φ → ∃ p : Nat, Prf (Pf (numeralM p) (formCode φ))
theorem rosser_de (hneg : NegNumStmt) (hpos : PosNumStmt) (hcon : ConsistentH) : ¬ Prf R ∧ ¬ Prf (neg R)
theorem rosser (hcon : ConsistentH) : ¬ Prf R ∧ ¬ Prf (neg R) := rosser_de negNum posNum hcon
-- T08: el cierre de `rosser` (con negNum y posNum) sin FOL.Metamath.Semantics.* ni Meta.SolidezPrf.*;
--   goedel_I debe disparar; una variante que pase por RosserReflexion, también
```
En matemáticas: T ⊬ R y T ⊬ ¬R, con un certificado mecánico de que la prueba sólo usa `ConsistentH`, derivaciones de T y aritmética de la metateoría. El oráculo sobre ℕ de `ModeloCodigo` está permitido (AUDITORIA:260).

**(ii) Qué demuestra y qué no.**
- **Como enunciado**, lo mismo que (c): el contenido lo pone el certificado, no el teorema.
- **Además da**, sin el modelo, NegNum, PosNum y el corolario de ω‑incompletitud: ∀n, `Prf ¬Pf(n̄,⌜⊥⌝)` junto con `goedel_II`.
- **No dice** nada sobre otras teorías. T08 es un control por espacio de nombres, no un teorema (INFERIDO).
- **¿Es el de los libros?** Es la prueba de libro para una T fija, no el teorema.

**(iii) Qué hay que construir, qué existe y qué se reutiliza.**
- **Construir:**
  - `rosser_de` y sus dos enunciados: 60–150 líneas (ESTIMACIÓN, RUT‑02).
  - T08: una tarde. La maquinaria está en `sondeos/ChoiceFrontera.lean:38-69` (`cierre`, `:59`).
  - W1 paramétrico en V: 15–30 líneas.
  - La calibración de la ruta P en una etiqueta: los pasos de AUDITORIA:83-88, 100–250 líneas.
  - La Etapa 2 sintáctica: 350–600 líneas, frente a 100–180 por la ruta H.
  - La Etapa 3c en ℕ: 60–150 líneas más.
  - GuardNeg, las 8 proyecciones (unas 96 líneas), la refutación de `thy` y PosNum: 40–80 según la crítica, 70–120 según el plan.
- **Existe y se reutiliza:**
  - `RosserBasura` §1–§4 y `prf_diagonal`.
  - `ArithPrf.lean:181-475` (295 líneas, a generalizar).
  - Los refutadores de profundidad 1 (`CodeWitnessPrf.lean:1146`, `:1170`, `:1599`) y 29 `prf_*` de `ChainNegPrf`.
  - Las reificaciones `CTree` y `STree`, y `stdChain_proofCode'` (`OmegaReflect.lean:230`).
  - `PLAN-NEGVERIFIER.md` (744 líneas) como guía.
- **No se reutiliza:** `RosserReflexion` queda como medición y como el mutante con que ver fallar T08.

**(iv) Coste.**
- **ESTIMACIÓN:** la ruta H son 1 400–2 250 líneas; la P suma 250–450 y 60–150 más, ≈1 710–2 850 en total (la suma es mía). Hay que añadir T08, W1 paramétrico y la calibración.
- **MEDIDO**, para calibrar:
  - El NegVerifier viejo tenía 3 214 líneas para una clase más estrecha (`resultado.json:170`).
  - W1 se estimó en 600–1 500 líneas y midió unas 490 (`DECISIONS.md:9391-9392`).
  - La Etapa 0 se estimó en 120–200 y lleva 406 líneas de fichero y 194 de declaraciones con dos de sus tres piezas.

**(v) Riesgos.**
- Si T08 se aplica a `rosser_de` y no a la instancia, pasa siempre (corrección de RUT‑02).
- `#print axioms` no distingue las rutas.
- GuardNeg es lo de más riesgo (`resultado.json:250`), y su inevitabilidad descansa en un argumento de modelo no compilado (`resultado.json:212`; T75 d).
- Los numerales son astronómicos: el log₂ del código de `ax_tc_cons` es ≈8,66·10⁷⁸ (RUT‑07).
- Las etapas que viven en `sondeos/` sin CI se pudren: el 2026‑10‑02 había 53 de 85 sondeos rotos.
- El control negativo con `Prf ⊥` es vacuo.

**(vi) Qué cambia en el resto del proyecto.**
- `axioms`, V₀, el ancla, G, el verificador, los 107 y el modelo: nada.
- Entran T08 (con T07) en el build y W1 paramétrico (el actual pasa a ser una instancia), R en `EV_TOK` y Rosser en la clase (i) de T09.
- T66: portar los 29 `prf_*` y retirar el resto.
- INFERIDO: con T61 hecho, un Rosser por la ruta P podría quedar sin `Classical.choice`. Todo lo que pase por `prf_sound` lo conserva (`SolidezPrf.lean:148`), así que el footprint sería una segunda señal, tosca, de pureza.

### (c) No hacer Rosser sobre T

**(i) Enunciado.** Ninguno: se cierra el frente con un ADR. Si se quiere un titular, con su etiqueta honesta (clase iii de T09):
```lean
theorem rosser_semantico : ¬ Prf R ∧ ¬ Prf (neg R)   -- prf_sound + W1 + consistencia
```
**(ii) Qué demuestra y qué no.** Nada que no dé ya `godelCN_indecidible` (ADR‑122 §2, `DECISIONS.md:9491-9492`). No es Rosser, porque usa la solidez.

**(iii) Qué hay que construir.** El ADR y los documentos.

**(iv) Coste.** Cero; el titular semántico, 60–120 líneas (ESTIMACIÓN).

**(v) Riesgos.** `NEXT-STEPS.md:29-39` y ADR‑121 §3 siguen prometiendo «Rosser con sólo `ConsistentH`». Si no se cierran por ADR, el P0 reaparece en cuanto alguien escriba un Rosser por la ruta H.

**(vi) Qué cambia en el resto del proyecto.**
- Nada en el build.
- Los dos sondeos pasan a registro y T64 se cierra.
- T66 retira 2 930 líneas sin portar (MEDIDO hoy con `wc`).
- La ronda 3 (T17) deja de esperar a Rosser.

## 3. Comparación

| | (a‑i) | (a‑ii) | (b) | (c) |
|---|---|---|---|---|
| Dónde vive «basta la consistencia» | en el enunciado | en el enunciado | en el control T08 | en ningún sitio |
| Teorías que cubre | B+E+α_E, E finita (T con E=[]) | T+E, E finita | sólo T | — |
| ¿Rosser de libro? | no (clase recortada y autoanclada) | el más cercano | la prueba, no el teorema | no |
| Toca `axioms`, V₀ o G | no | según el diseño | no | no |
| Toca el verificador (107) | no | 25 de 107 (MEDIDO) | no | no |
| Toca el modelo | generalizarlo (INFERIDO) | reinterpretar y revalidar | no | no |
| Refactor de `Prf` | sí | sí | no | no |
| Ruta de NegNum | H o P (INFERIDO) | H o P | sólo P | — |
| Coste (ESTIMACIÓN) | «semanas» + 1 400–2 250 | sin medir, el mayor | ≈1 710–2 850 + T08 | 0 (60–120) |
| Riesgo principal | CRI‑02, vacuidad por diseño | radio, ancla nueva | contenido en un control; GuardNeg | P0 latente |

**Qué se pierde si se elige (c).**
- El argumento: ⊬G queda en la clase de la consistencia simple y ⊬¬G en la de la solidez (T09, :270-272).
- NegNum y PosNum. Tienen contenido por cualquier ruta, porque son hechos de derivabilidad que la solidez no da (INFERIDO). Con ellos se perdería también el corolario de ω‑incompletitud.
- La base para la opción (a) o para el frente de Gentzen (`resultado.json:280-288`).
- Las 406 líneas de la Etapa 0, que pasarían a registro.
- El horizonte que fijó el propietario el 2026‑10‑02.

## 4. Observaciones transversales (INFERIDO) y una opinión

- **Una versión ingenua de (a) sería falsa:** Rosser para `PrfL (axioms ++ E)` con la R de T falla con E = [R]. Cada extensión necesita su propio predicado de prueba; ése es CRI‑02 visto desde el contraejemplo.
- **Ninguna opción baja de los esquemas de `Prf`** (Q, IΣ₁), ni llega a extensiones r.e. infinitas.

**Opinión (mía, no es una medida).**
- Si se quiere que el enunciado mismo diga «basta la consistencia simple», sólo (a) lo consigue. De sus dos diseños, (a‑i) me parece la de mejor relación entre contenido y coste.
- Lo barato que decide, sin tocar el build, es el sondeo de viabilidad de T62 con los tres controles de CRI‑02 (1–2 días, ESTIMACIÓN), junto con la calibración de la ruta P.
- T08 merece la pena en cualquier caso.

# Decisiones de Diseño — ROBINSON_PlusPlus

**Last updated:** 2026-10-18 — hasta **ADR-160** (T66: el subárbol sin consumidor —`ChainNegPrf`, `VerifierSound`, `OmegaReflect`, `ChainDecode`, `CodeDecode`, 2 953 líneas sin nada en el cono de los 21 titulares— sale del build, con la etiqueta `archivo/t66-2026-10-18`; `dec` se queda y `decodeForm` sale; los sondeos de Rosser, ordenados: `RosserBasura` con §5, dos de CONTROL a REGISTRO, `DespachadorCoste` archivado; 135 jobs, 118 módulos). Antes, el mismo día — hasta **ADR-159** (🏁 LÖB, `lob : Prf (Prov⌜φ⌝ ⇒ φ) → Prf φ` y `lob_iff`, por el punto fijo de `Prov(#0) ⇒ φ` y D1–D3, en `Meta/Lob.lean`, de la clase (i), en `PUROS`; Gödel II, de corolario; la línea de llegada de RPP, completa en sus teoremas; 140 jobs, 123 módulos). Antes, el mismo día — hasta **ADR-158** (las decisiones del propietario sobre ADR-157: `rosser_ext` con `_hE`, el titular; `rosser_red`, la forma más fuerte; `rosser`, titular). Antes, el mismo día — hasta **ADR-157** (🏁 Rosser, etapa 7, hecha: ROSSER por la reducción, `rosser_ext` —si T+E es consistente, su sentencia de Rosser es indecidible en T+E—, `rosser_red` para toda lista E y `rosser` para T sin hipótesis, en `Meta/Rosser.lean`, de la clase (i) para T08: `rosser_ext` entra en `PUROS` y `rosser` en `IMPUROS`, con el recorrido y `#pureza` en un módulo aparte, `Meta/PurezaComando.lean`; `hE`, que la prueba no usa; 139 jobs, 122 módulos). Antes, 2026-10-17 — hasta **ADR-156** (Rosser, etapa 5, NegNum, hecha: el predicado de prueba de T, decidido sobre numerales, `proofN_decide` y `negNum`, con la cadena decidida línea a línea y las premisas de `mp`/`gen`; y con W1(ax), si φ no es teorema, T refuta cada candidata a prueba de φ; en `Meta/RosserNegNum.lean`, pura; 137 jobs, 120 módulos). Antes, el mismo día — hasta **ADR-155** (dos arreglos pendientes: el docstring de `consistencia` dice que la consistencia es relativa a Lean, el pendiente de ADR-138; y la pertenencia en ℕ, decidible sin lógica clásica, `decMemN`: `prf_In_decide` deja de depender de `Classical.choice`). Antes, el mismo día — hasta **ADR-154** (Rosser, etapa 4, NegLineWF, hecha: la buena formación de una línea, decidida sobre su numeral, `lineWF_decide`, y la línea mala refutada, `prf_neg_lineWF`; las 21 instancias de `ax_lineWF_*`, comprobadas por el núcleo; `thy` por el ancla; en `Meta/RosserNegLinea.lean`, pura; 136 jobs, 119 módulos). Antes, el mismo día — hasta **ADR-153** (Rosser, etapa 3, GuardNeg, hecha: la guarda falsa se refuta en `Prf` sobre el numeral, la de término y la de fórmula, `prf_neg_hasWit` y `prf_neg_hasWitF`, y queda decidida, `hasWit_decide`; la caracterización en ℕ, completa; una dicotomía por inducción fuerte, sin lógica clásica; en `Meta/RosserGuardNeg.lean`, pura; 135 jobs, 118 módulos). Antes, el mismo día — hasta **ADR-152** (Rosser, etapa 2, NumEval, hecha: `substtc`/`liftc`/`substfc`/`liftfc` evaluados sobre numerales con las guardas verdaderas, en `Meta/RosserNumEval.lean`, pura: los códigos buenos en ℕ, su clausura, las guardas que dan árboles y `prf_substfc_guarda`; dos congruencias de listas, a `Meta/NumCodeClosedPrf.lean`; 134 jobs, 117 módulos). Antes, el mismo día — hasta **ADR-151** (el sondeo de `hasWitF`, la puerta del riesgo de GuardNeg: la guarda de FÓRMULA se refuta sobre numerales basura a profundidad 1 y 2, en las dos clases de casilla, sin el modelo; `sondeos/RosserHasWitF.lean`, de CONTROL; la puerta, abierta). Antes, el mismo día — hasta **ADR-150** (Rosser, etapa 1, hecha: la capa de listas sobre numerales en `Meta/RosserNumerales.lean`, pura: descomponer un numeral, evaluar `carc`/`cdrc`/`lenc`/`nthc`, `concat`, `runFn` y los constructores de código, y decidir `In`, también en las conclusiones de una cadena; tres lemas de `sondeos/RosserBasura.lean`, promovidos; 133 jobs, 116 módulos). Antes, el mismo día — hasta **ADR-149** (Rosser, etapa 6, PosNum, hecha: `posNum`, D1 con el testigo en forma de NUMERAL, en `Meta/RosserPosNum.lean`, puro; y T08 sigue por fin los lemas del propio módulo: el `#pureza` por módulo no los veía, medido con un mutante, y `mutanteLocal` lo vigila en cada build; 132 jobs, 115 módulos). Antes, el mismo día — hasta **ADR-148** (Rosser, etapa W1(ax), hecha: `w1Ax`, W1 con el código de los 142 y SIN el modelo, en `Meta/RosserW1.lean`, puro por su `#pureza`; la cadena de W1, paramétrica en `V`; 131 jobs, 114 módulos). Antes, el mismo día — hasta **ADR-147** (las decisiones del propietario sobre ADR-146: el orden de su §4, con el sondeo de `hasWitF` pronto; el código en el build, con un `#pureza` al final de cada módulo; T66, al final, midiendo qué usó NegNum; la respuesta es del 2026-10-16 y se registra al día siguiente). Antes, 2026-10-16 — hasta **ADR-146** (🟡 PROPUESTO, el diseño de NegNum y PosNum de T por la ruta sintáctica: de las 80 piezas del build que el plan reutiliza, 76 son PURAS y las 4 impuras lo son por `linea_thy`; W1 con `codeNatList axioms`, PosNum por D1 y un lema, y el orden con el riesgo primero). Antes, el mismo día — hasta **ADR-145** (las decisiones del propietario sobre ADR-144: Rosser por REDUCCIÓN; V-B si hace falta un verificador con parámetro; las variantes de reglas, aplazadas; T62, cerrado). Antes, el mismo día — hasta **ADR-144** (🟡 PROPUESTO, el diseño de T62: una extensión finita T+E por REDUCCIÓN a T —su cálculo es `PrfH E`, su predicado de prueba el de T delante de `impChain`—, sin tocar el verificador, los 142 ni el modelo; la medición de alcance y la viabilidad, compiladas). Antes, el mismo día — hasta **ADR-143** (T08: el control de pureza del cierre, en el BUILD, `Meta/PurezaTitulares.lean`: los 8 titulares de la clase (i) no nombran la semántica, y si la nombran el build no compila; visto fallar con mutantes). Antes, el mismo día — hasta **ADR-142** (la historia, a `doc/historia/` por traslado PURO: ADR-001…130 —aquí queda su índice—, los bloques viejos de NEXT-STEPS y los banners apilados de siete documentos; la fuente única del estado es el banner de TEOREMAS-E-HIPOTESIS.md; CHANGELOG, congelado; 18 entradas de `B_DEUDA` salen por exclusión, tope 23). Antes, el mismo día — hasta **ADR-141** (los sondeos, medidos con `lake lean` —39 de 93 compilan— y clasificados: 11 de control en la CI con `check-sondeos.bash --controles`, 28 de registro, 1 a reparar y 53 archivados con la etiqueta `archivo/sondeos-2026-10`). Antes, el mismo día — hasta **ADR-140** (las decisiones del propietario: capas DENTRO de RPP, la línea de llegada —`T_UNIVERSO` + Rosser + Löb—, las variantes Q++/PA/HA medidas en el diseño de T62, y ADR-139 aprobado en sus pasos 1 y 2). Antes, el mismo día — hasta **ADR-139** (🟡 PROPUESTO: acotar el proyecto en tres pasos —archivar los sondeos, congelar la historia, contratos de capa—, con el cono de los titulares MEDIDO por declaración, `sondeos/ConoTitulares.lean`). Antes, el mismo día — hasta **ADR-138** (la consistencia que da `consistencia` es RELATIVA a Lean, PRA ⊢ Con(Lean) → Con(T_Prf), y no puede ser absoluta: los banners, TEOREMAS §4, AXIOMS §0.2 y PLAN-LIBRO cap. 6). Antes, 2026-10-14 — hasta **ADR-137** (Rosser, decidido: la teoría como PARÁMETRO del verificador, opción a‑ii de T01, con T08 como criterio de aceptación; y dos frases de FOL al día). Antes, el mismo día — hasta **ADR-136** (`master` protegido: sólo entra un commit con la CI ya verde, por una rama `ci/…`; y las decisiones del propietario del 2026‑10‑14). Antes, el mismo día — hasta **ADR-135** (TEOREMAS-E-HIPOTESIS al día —`⊬¬G` existe—, con la columna «¿qué usa la prueba?» MEDIDA en tres clases, y el control `[T]`). Antes, el mismo día — hasta **ADR-134** (la teoría de los titulares, `T_Prf`, descrita: contiene a PA, no es Q ni IΣ₁; `AXIOMS.md` §0, la descripción canónica, con lo que se supone hoy; D1 usa la inducción, D2 la de listas, y ningún titular construye un paso DNE salvo `goedel_I_neg`, MEDIDO en `sondeos/InduccionTitulares.lean`; y los comentarios caducados o falsos de 113 `.lean`, al día, con su revisión adversarial). Antes, 2026-10-12 — hasta **ADR-133** (MANDATORIES: M‑11 al derecho, M‑10 y M‑6 corregidas, M‑1, M‑7 y M‑13 al día; el control `[M]` de check-doc-sync, nuevo). Antes, 2026-10-12 — hasta **ADR-132** (la auditoría del suelo, versionada: 81 trabajos, 4 P0, 7 P1, en `doc/AUDITORIA-SUELO-2026-10-12.md`; T00, los artefactos fuera de git rescatados a `doc/registro/`; `d3_prf_of_sigma1` y `d3_prf_of_reflect_bounded`, VACUOS, medido). Antes, 2026-10-05 — hasta **ADR-131** (de dónde viene el `Classical.choice` de los titulares, MEDIDO: no de `p3`; dos cancelaciones de lift lo traen a 158 de 182 filas; fe de erratas de ADR‑129). Antes, 2026-10-05 — hasta **ADR-130** (las dos notas de `Meta/CodeDecode.lean`, MEDIDAS: lo que el núcleo rechaza es desplegar por defeq la mutua `decodeTerm`, no el `if`/`==`/`String`; `sondeos/IteSimboloNucleo.lean`). Antes, 2026-10-05 — hasta **ADR-129** (D7 EJECUTADA: los símbolos de FOL son `List Char`, en FOL y en RPP; 44 filas de footprint pierden `Classical.choice`; ningún valor cambia). Antes, 2026-10-05 — hasta **ADR-128** (`autoImplicit` desactivado también en `lake build`, en RPP y en FOL, con `leanOptions`: coste medido, ninguno). Antes, 2026-10-05 — hasta **ADR-127** (la auditoría de ADR-124/125/126: «por primera vez» era sólo «sobre un numeral», el control no mide el método, dos lemas re‑derivados; y los 88 sondeos, re‑medidos). Antes, 2026-10-05 — hasta **ADR-126** (la refutación HEREDITARIA a profundidad 2 y el control de discriminación, en `sondeos/RosserBasura.lean`). Antes, 2026-10-05 — hasta **ADR-125** (Rosser, Etapa 0, segunda pieza: la guarda de término refutada en `Prf` sobre un numeral, en un sondeo). Antes, 2026-10-05 — hasta **ADR-124** (el CONTROL NEGATIVO del modelo, en el build: `MNV V` refuta `ax_tc_cons`; y la auditoría de ADR-123, que rectifica tres afirmaciones). Antes, 2026-10-05 — hasta **ADR-123** (Rosser, Etapa 0: la reflexión numeral de `substfc`/`liftfc`, CONFIRMADA en un sondeo). Antes, 2026-10-05 — hasta **ADR-122** (D7 MEDIDA: sólo 48 de 226 footprints perderían `Classical.choice` sin `String`; Rosser re‑medido tras el modelo). Antes, 2026-10-05 — hasta **ADR-121** (Gödel I ENTERO: `⊬ ¬G` por la solidez del verificador en el modelo, `goedel_I_neg`; y TARSKI sin hipótesis, sintáctico y en ℕ). Antes, 2026-10-05 — hasta **ADR-120** (`ConsistentH` es un TEOREMA del build, `consistencia`, y Gödel I/II van SIN HIPÓTESIS: `goedel_I`, `goedel_II`, en `Meta/Consistencia.lean`). Antes, 2026-10-05 — hasta **ADR-119** (el MODELO de los 142: `ConsistentH` demostrada en `sondeos/ModeloNat.lean`, y Gödel I/II sin hipótesis allí; la promoción al build, después). Antes, 2026-10-05 — hasta **ADR-118** (la clase `AnclaEq` retirada: 426 ligaduras fuera, en un commit mecánico; el ancla es el teorema `prf_ancla`). Antes, 2026-10-04 — hasta **ADR-117** (F1 reparado: `axiomsCodeT` anclado por un axioma DIAGONAL, `axioms` = 142 = 141 de la base + el ancla; `AnclaEq` pasa a ser un TEOREMA, `prf_ancla`, con su instancia, y Gödel I/II dependen sólo de `ConsistentH`, todavía condicionales: los 142 no tienen un modelo construido; todo computable, y un control nuevo impide EJECUTAR `axioms` o el ancla). Antes, el mismo día — hasta **ADR-116** (los controles que daban verde sin comprobar: `[B]` casaba por prefijo, `check-axioms` de FOL era un grep, `check-estratos` no veía `TheoryFramework` ni los `private axiom`; y cuatro revisiones adversariales de los arreglos: en la segunda, el conteo de `axiom` de `[A]` estaba a 0 fijo; en la cuarta, los censos no veían la confianza en el compilador ni lo que el kernel no comprobó, y el autotest de `check-sorry` contaba en vez de comparar; `strip-lean.awk` v5; `@TRUST`, `@NATIVO` y `@AJENO` en los censos por entorno; `leanchecker` en las dos CI; el `thaw` de los cinco congelados de FOL; la etiqueta `pre-adr115`). Antes, 2026-10-02 — hasta **ADR-115** (la capa `⊢` RETIRADA de RPP: 27 módulos y 633 declaraciones, 0 `axiom` de Lean, la cadena sobre `Prf` intacta; las meta‑reglas de FOL, refutadas, retiradas también de FOL el mismo día, §8). Antes, el mismo día — hasta **ADR-114** (la auditoría de la base, ronda 1: `Prf ⊥` en el `master` viejo, la capa `⊢` refutable, `OmegaConsistent` refutable; ADR-113 fusionado como REPARACIÓN; la capa `⊢` y las meta-reglas, a retirar). Antes, 2026-09-28 — hasta **ADR-113** (la salida (5) adoptada: `cons a b = σ (pair a b)`; seis módulos adaptados, 145 jobs, 517 footprints sin cambios). Antes, 2026-09-27 — hasta **ADR-112** (FOL: el segundo y el tercer lote congelados, 23 módulos; N5, auxiliares; N7, el enunciado de `herbrand_of_skolemNF₀` reforzado). Antes, ADR-111 (la tercera criba de congelación de FOL, tras D1‑D8: 10 congelables propuestos, decisiones N5 y N7).

> **Estado actual:** el banner de [TEOREMAS-E-HIPOTESIS.md](TEOREMAS-E-HIPOTESIS.md) es la fuente única (T33, [ADR‑142](DECISIONS.md)).
> Los banners que se apilaban aquí están, tal cual, en [doc/historia/BANNERS.md](doc/historia/BANNERS.md).

**Autor**: Julián Calderón Almendros

Registro de decisiones arquitectónicas (ADR) de este proyecto. Cada entrada documenta
*qué* se decidió y *por qué*, para referencia futura.

> Este fichero adopta el esqueleto unificado de `lean4-project-template` (ADR-001–009,
> traducidos al español) y **preserva íntegros** los dos ADR reales y sustanciosos que
> ya existían aquí (renumerados a ADR-010/011) — son, junto con los de Peano, los ADR
> de mejor calidad entre los proyectos hermanos: documentan contraejemplos matemáticos
> concretos, no solo preferencias de estilo.

---

## ⚠️ MANDATORIES (reglas vinculantes de este proyecto — lectura obligatoria)

**Cada MANDATORY lleva su columna «Verificación»** — una MANDATORY sin verificación
mecánica es una intención, no una regla. Esta tabla recoge reglas **ya vigentes** en el
proyecto; no introduce ninguna nueva.

| # | MANDATORY | ADR | Verificación |
|---|---|---|---|
| **M-1** | ⛔ **Ningún `axiom` nuevo —de Lean o de la teoría objeto— sin sanción explícita del autor y su ADR.** Un axioma sin ADR ya hizo **inconsistente** la teoría objeto | ADR-010/011/012/013 | `AXIOMS.md` (inventario) · `check-doc-sync.bash` [A] contrasta la cifra «N `axiom` de Lean» con el patrón de `check-axioms.bash` (de FOL), sobre el código sin comentarios · `#print axioms` en cada frente. ✏️ *(2026‑10‑12, ADR‑133)*: decía «con grep '^axiom '», que ADR‑116 sustituyó (era ciego a private, a los atributos y a la sangría) |
| **M-2** | ⛔ **Las imágenes punteadas (`substfcT`, `substtcT`, `liftcT`, `liftfcT`, `predcT`) son DEFINICIONES, jamás axiomas.** Postular la ecuación de rastreo (`ax_tc_substfc`, `ax_tc_cons`) da `axioms ⊢ ⊥`; los puentes se escriben `:= rfl` y el salto sólo vale **dentro de `Prov`** | ADR-012/013/015 | `grep -rn '^axiom ax_tc_' ROBINSON_PlusPlus/` debe dar **0** |
| **M-3** | ⛔ **NUNCA `cd FOL && lake build`.** `FOL` es dependencia LOCAL (`require FOL from "../FOL"`) y compilarla desde su propio directorio usa **otro toolchain**. Todo se compila desde la raíz de `ROBINSON_PlusPlus` | — | `update-toolchain.bash` compila desde la raíz; el `lakefile.lean` es la única fuente del target |
| **M-4** | **Cero `sorry` en el árbol activo.** No se «aparca» una prueba con `sorry`: o entra probada, o se queda en `sondeos/` | — | `bash check-sorry.bash` → `✅ No sorry found.` (cuenta el TOKEN, fuera de comentarios y cadenas; AI-GUIDE §27.1) |
| **M-5** | **Todo módulo de producción aparece en el catálogo `REFERENCE.md` §1** y termina con su bloque `export` — puesto **por CONSUMO, no por existencia** | AI-GUIDE §1/§14/§17 | `check-doc-sync.bash` [C] (proyección). ⚠️ El «por consumo» del `export` **no** tiene verificación mecánica todavía: se audita a mano (así se detectaron B8b y el dedup de §3.52) |
| **M-6** | **`bash check-doc-sync.bash` en verde antes de cerrar cualquier pasada de documentación**, lanzado desde PowerShell: desde Bash `lake` no está en el PATH y el script da ROJO por no poder medir. Rompen `[A]`, `[B]`, `[C]`, `[D]`, `[E]`, `[F]`, `[H]` y `[M]`; sólo `[A2]` es aviso, y pide juicio. ✏️ *(2026‑10‑12, ADR‑133)*: decía «`[A]`, `[C]` y `[D]` rompen; `[B]` es aviso»: `[B]` rompe desde ADR‑084 (con trinquete), y `[E]`, `[F]`, `[H]` y `[M]` llegaron después | AI-GUIDE §27 · ADR-084 · ADR-133 | el propio script (exit 0) |
| **M-7** | ⚠️ **El `PsiF` de un chasis inductivo (`pcc_bdAll_intro`) sólo es natural si el PARÁMETRO NO VIAJA DENTRO DE LA FÓRMULA que se codifica.** Si va dentro, `hPl` es **FALSA** y hace falta escribirlo con símbolos OBJETO y puentear dentro de `Prov`; si entra **sólo como testigo** (cuerpo cerrado), el `substCodeF`/`substCodeF2` **es** natural y no hace falta nada. ⚠️ **Afinada el 2026‑09‑10f** (§3.66.1): la forma vieja —«nunca un `substCodeF`»— sobre‑prohibía | ADR-021 | dos `rfl` (`substCodeT_hole_lhs`/`_rhs`, `Meta/D3ChainDotPrf.lean` §10.1) — y la hipótesis hPl, escrita con un `substCodeF` del parámetro, no compila. ✏️ *(2026‑10‑12, ADR‑133)*: decía «y el propio hPl no compila», con hPl entre comillas invertidas como si fuera una declaración; es una hipótesis de pcc_bdAll_intro |
| **M-11** | ⛔⛔ **Antes de POSTULAR un `axiom` cuya conclusión es un inductivo (lo HABITA), comprobar que no contradice lo que se demuestra por inducción sobre él.** El recursor cubre a TODO habitante, también a los que fabrica un axioma: un teorema probado por inducción sobre un inductivo habitado es **VÁLIDO**. Lo que puede ser falso es el **axioma**: si contradice lo que la inducción demuestra, Lean + él ⊢ `False`, como los cuatro de `FOL/MetaRules.lean` (borrados con ADR‑115). ⚠️ `#print axioms` es CIEGO a esto: el footprint de un teorema probado por inducción no lleva los axiomas que habitan el inductivo. 🔑 **Regla de diseño**, que sigue en pie: una regla que se quiere añadir a una relación inductiva se añade como CONSTRUCTOR (o con un inductivo que la envuelva), nunca como `axiom`; un `axiom` no extiende el punto fijo, afirma algo sobre él. Hoy ningún estrato está habitado. ✏️ *(2026‑10‑12, ADR‑133)*: hasta hoy esta fila decía lo contrario —«Antes de demostrar algo por INDUCCIÓN sobre un tipo inductivo, comprobar que NINGÚN `axiom` lo habita… ⇒ el teorema es FALSO», «`Derives` NO ADMITIRÁ INDUCCIÓN NUNCA», con las listas negra y blanca del 2026‑09‑12/13, en dieciséis líneas—, y era al revés (ADR‑114 §2: *M‑11 evitaba ESCRIBIR la contradicción, no la quitaba*). El build induce hoy sobre `Derives` (`derives_to_derives0`) y sobre `Prf` (`prf_sound`, en la que descansa `ConsistentH`). La regla vieja y sus listas quedan como registro en ADR‑025 y ADR‑029 | ADR-025 · ADR-114 §2 · ADR-115 | `bash check-estratos.bash` (desde PowerShell): cuántos `axiom` habitan cada inductivo, medido por el tipo de cada axioma, y rompe en los dos sentidos; mecanizado desde el 2026‑09‑16 |
| **M-10** | ⛔ **Los enunciados de indemostrabilidad, indecidibilidad o consistencia van sobre `Prf`** (el cálculo de Hilbert de `Meta/Hilbert.lean`), y no sobre otro cálculo sin un puente demostrado. ✏️ *(2026‑10‑12, ADR‑133)*: la razón que daba esta fila —que `axioms ⊢` era sintácticamente COMPLETO, en el `Meta/OmegaStrength.lean` de entonces, verificado con los teoremas `derives_completo` y `hgi_es_refutar`— es de un `axioms ⊢` que ya no existe: la capa `⊢` salió de RPP con ADR‑115 (`b1dedd1`) y las cuatro meta‑reglas de FOL con `3b355d7` (`Derives` sigue en FOL, sin ellas); los dos teoremas no tienen hoy declaración y el módulo ya no existe | ADR-024 · ADR-115 | las filas de `goedel_I`, `goedel_I_neg`, `goedel_II` y `goedel_second_prf` en `check-footprints.bash` (existen, y con los tres axiomas de Lean); que su ENUNCIADO hable de `Prf` lo fijará el contrato de T07 (`doc/AUDITORIA-SUELO-2026-10-12.md`); hasta entonces, a mano, al enunciar |
| **M-9** | ⛔ **Un `Probe/` que decide un ADR se PROMUEVE a `sondeos/` antes de cerrar ese ADR** — o la decisión queda **sin evidencia versionada**. `Probe/` está en `.gitignore` **a propósito** (es borrador); `sondeos/` es el **resultado**, y se versiona con su fila en `sondeos/README.md`. Si el probe pasó a **producción**, la evidencia es el módulo y no hay nada que promover | [auditoría F‑9](doc/AUDITORIA-2026-09-11.md) · `PLAN-PRUEBAS.md` §2.1 | a mano: todo ADR debe citar su sondeo o su módulo |
| **M-8** | ⚠️ **Subsumir la CLASE no es descargar la OBLIGACIÓN.** Antes de dar por resuelto un frente con «la clase X ya cubre la clase Y», leer **qué obligación queda después**: `numTree_of_isCodeShaped` es **cierto como teorema** y su conclusión —«no hay que cambiar `StdChain`»— **falsa**, porque la obligación que deja (`m ≠ n` con `codeNat` astronómico) **no es descargable** | ADR-022 | `stdChain_proofCode'` + `junk_line_not_stdLine` (`sondeos/OmegaConsistentRefutable.lean` §0; ✏️ 2026‑10‑18, ADR‑160: hasta entonces en Meta/OmegaReflect.lean §1ter/§1quater, retirado del build) |
| **M-12** | ⛔ **Empujar `FOL` ANTES que `ROBINSON_PlusPlus`.** La CI de RPP **clona FOL como hermana**; si se empuja RPP primero, la CI compila contra un FOL viejo y `check-footprints` falla con «NO MEDIDO» en los titulares nuevos. ⚠️ Es una **CARRERA**, no un fallo determinista: los cuatro pushes anteriores del mismo día pasaron con el orden malo, y el quinto no. 🔑 *Un fallo intermitente es peor que uno fijo: da verde el número de veces suficiente para que nadie mire el orden.* | — | MEDIDO el 2026‑09‑17, run `35214528037`: dos titulares de `FOL.Skolem0` «NO MEDIDO» con el repo local en verde. Verificación: `gh run list` tras cada pareja de pushes |
| **M-13** | ⚠️ **Una cifra de control se REEJECUTA o se marca con su ALCANCE.** Copiarla de una pasada a la siguiente la convierte en decoracion: «0 warnings» viajo por ADR-057/058/059 siendo la cifra de la `lean_lib FOL` **sola** (reales: 7 en RPP + 4 en FOL). Y su reciproca: **un control sin nada que contrastar no aprueba, se ABSTIENE** — `check_num` sin aparicion imprime «control VACIO» y sale con **0** | ADR-060 §6, ADR-061 §1 | `bash check-warnings.bash` (desde PowerShell; los avisos declarados, por fichero y clase), y el aviso «control VACÍO» de check-doc-sync, que hay que LEERLO. ✏️ *(2026‑10‑12, ADR‑133)*: aquí decía «⬜ falta check-warnings.bash», que existe desde ADR‑065 (b22dd85, 2026‑09‑18) |

> **Sobre `Classical.*`**: este proyecto **no** lo prohíbe (2 usos verificados el
> 2026-07-12). Lo que sí mantiene es la disciplina de **cero axiomas espurios** de M-1.
> El episodio «F7a» (retirada de 7 postulados legacy, en `CHANGELOG.md`) es su
> aplicación práctica. ⚠️ **No revertir F7a**: fue un arreglo de solidez.

---

## Índice de ADR‑001…ADR‑130 (el texto entero, en [doc/historia/DECISIONS-001-130.md](doc/historia/DECISIONS-001-130.md))

Trasladados el 2026-10-16 por [ADR‑142](#adr-142), tal cual. Una línea por ADR: el título y, si lo declara en su cabecera, el estado. Lo que dicen es de su fecha.

| ADR | título | estado |
|---|---|---|
| ADR-001 | Sin dependencia de Mathlib | Aceptado |
| ADR-002 | `autoImplicit = false` | Aceptado |
| ADR-003 | Sistema de bloqueo de archivos | Aceptado |
| ADR-004 | Convenciones de nombres Mathlib | Aceptado |
| ADR-005 | Namespaces alineados con directorios | Aceptado |
| ADR-006 | Subdirectorios temáticos para la organización de módulos | Aceptado |
| ADR-007 | Árbol de documentación `doc/REFERENCE-{tema}.md` | ✅ **Aceptado e IMPLEMENTADO** (2026-07-12; revisado 2026-08-22) |
| ADR-008 | Sistema de anotaciones en REFERENCE.md | Aceptado |
| ADR-009 | `NAMING-CONVENTIONS.md` como fichero separado | Aceptado |
| ADR-010 | Meta-axiomas en `Minimal/Axioms.lean` son meta-teoremas de aritmética, no reglas FOL | **Aceptado — pero su JUSTIFICACIÓN está SUPERSEDIDA por [ADR‑027](#adr… |
| ADR-011 | `subst_lift_cancel_formula` — corrección del enunciado en FOL | Aceptado |
| ADR-012 | Los códigos de Gödel se representan como NUMERALES, no como árboles `cons` | aceptada e implementada (`master`) |
| ADR-013 | La capa rastreada se pone en CUARENTENA, no se borra | aceptada e implementada |
| ADR-014 | La cuarentena se recupera INTERNALIZANDO la evaluación, no reescribiendo los tags | aceptada e implementada (`master`, HEAD `68fa43c`) |
| ADR-015 | La buena‑formación de códigos se DEFINE en vocabulario existente, no se AXIOMATIZA | ✅ ACEPTADA  |
| ADR-016 | El predicado se PARTE en tres, y la partición es la CONDICIÓN de la inducción | ✅ ACEPTADA |
| ADR-017 | El testigo va ABIERTO — no se ancla en casilla, y no se acota | ✅ ACEPTADA |
| ADR-018 | El descenso es UNA inducción con conclusión CONJUNTIVA, y la guarda va DENTRO de `Φ` | ✅ ACEPTADA |
| ADR-019 | Cuando el sondeo SUBSUME a producción, baja el GENERAL — no subas el corolario | ✅ ACEPTADA  |
| ADR-020 | Los 7 esquemas de sustitución llevan la guarda DENTRO — y para eso las guardas BAJAN a `Minimal` | aceptado  |
| ADR-021 | El `PsiF` de un chasis inductivo se escribe con símbolos OBJETO — y por eso hacen falta DOS cuerpos | — |
| ADR-022 | La clase de testigos de la ω‑consistencia se ESTRECHA a LÍNEAS ESTÁNDAR — y se paga el precio por escrito | Aceptado — **sancionado por el propietario** el 2026‑09‑10h. |
| ADR-023 | El censo de `coreAxioms` se CERTIFICA con `primAxioms` — y eso NO mueve la frontera de la teoría | 🏁 **ACEPTADO, RATIFICADO Y EJECUTADO** el 2026‑09‑10h. **9 de los 11 c… |
| ADR-024 | `⊢` es herramienta, `Prf` es enunciado — y qué significa exactamente `ConsistentOmega` | **Aceptado** — decisión del propietario tras la medición de `Meta/Omeg… |
| ADR-025 | Un `axiom` que HABITA un inductivo prohíbe la inducción — y `FOL.soundness` era FALSO | ✅ SANCIONADO (contención ejecutada; la reparación de fondo, abierta) |
| ADR-026 | El ancla de codificación deja de ser `axiom` y pasa a ser la CLASE `AnclaEq` | ✅ EJECUTADO (decisión del propietario: *«elegimos (A) parametrizar |
| ADR-027 | La justificación de ADR-010 está REFUTADA — `gen` no es la ω‑regla, y sí podría ser constructor | ✅ ACEPTADO  |
| ADR-028 | FOL pasa de 13 a 4 axiomas — y los cuatro son EXACTAMENTE los que el kernel obliga | ✅ EJECUTADO  |
| ADR-029 | `ax_list_induction` pierde su premisa‑función — y M‑11 sobre `Derives` se declara PERMANENTE 🗑️ *(lo que esta línea cita de `⊢` quedó retirado con esa capa, ADR-115)* | ✅ EJECUTADO (sanción del propietario)  |
| ADR-030 | La enumerabilidad de `Formula` deja de ser un postulado — `FOL/Enumeration.lean` | ✅ EJECUTADO (sanción del propietario)  |
| ADR-031 | Las dos congruencias de la igualdad, DEMOSTRADAS — la Completitud queda a UN postulado | ✅ EJECUTADO  |
| ADR-032 | `henkin_extension_lemma` SE MIDIÓ — sale, y por eso se QUEDA | ✅ **DECIDIDO — opción (A), sanción del propietario**: |
| ADR-033 | `Derives₀` — el cálculo sobre el que la metateoría SÍ significa algo (Paso 0) | ✅ EJECUTADO (sanción del propietario)  |
| ADR-034 | `derives0_soundness` — el repo tiene por fin un cálculo de FOL⁼ SÓLIDO (Paso 1) | ✅ EJECUTADO (sanción del propietario)  |
| ADR-035 | `derives0_rename` — la pieza que Henkin necesitaba, y es CONSTRUCTIVA | ✅ EJECUTADO (sanción del propietario)  |
| ADR-036 | `derives0_gen_fresh` — el paso de EIGENVARIABLE, y con él las tres piezas de Henkin | ✅ EJECUTADO (sanción del propietario)  |
| ADR-037 | `henkin_step_consistent` — el corazón de Henkin, probado; el ensamblaje, NO | ✅ EJECUTADO  |
| ADR-038 | Los ESTRATOS, declarados y vigilados — y la escalera de binders, cerrada a medias | ✅ EJECUTADO (sanción del propietario)  |
| ADR-039 | La extensión de Henkin, CONSTRUIDA — y el riesgo que el plan marcaba en rojo, disuelto | ✅ EJECUTADO  |
| ADR-040 | El ensamblaje de Henkin, CERRADO — y la no‑finitud, localizada en una línea | ✅ EJECUTADO  |
| ADR-041 | **COMPLETITUD** — `completeness₀`, y las dos direcciones sobre un mismo cálculo | ✅ EJECUTADO  |
| ADR-042 | Vía H · **H1 y H2** — la completitud proposicional, y es FINITARIA de verdad | ✅ EJECUTADO  |
| ADR-043 | Vía H · **H4 hecho** (la mitad ⟸) y **H3 enunciada** — el certificado de Herbrand | ✅ EJECUTADO (H4 ⟸)  |
| ADR-044 | H3, primera pieza — **`rewrite_at` es ADMISIBLE**, y el frente pasa de dos obstáculos a uno | ✅ EJECUTADO  |
| ADR-045 | H3, segunda pieza — **`subst` es ADMISIBLE**, y el cálculo queda en forma de libro | ✅ EJECUTADO  |
| ADR-046 | H3, tercera pieza — el CÁLCULO DE SECUENTES, y la deuda reducida a DOS `Prop` | ✅ EJECUTADO  |
| ADR-047 | La corrección de PeanoRF, ACEPTADA y BLINDADA — y su conjetura sobre `Theorems.Eq`, REFUTADA | ✅ EJECUTADO  |
| ADR-048 | `LK₀` no prueba de más — y el dividendo de tener las DOS direcciones | ✅ EJECUTADO  |
| ADR-049 | `NDtoLK` demostrada — y la regla que faltaba, `eqAx` | ✅ EJECUTADO  |
| ADR-050 | El andamiaje del Hauptsatz — H3 sobre el CORTE ÚNICO, y dos conmutaciones que faltaban | 🔶 PARCIAL (el Hauptsatz **NO** está)  |
| ADR-051 | Las dos conmutaciones y `lkh_subst` — H3 a UNA pieza, y un control que absolvía a 27 módulos | ✅ ACEPTADA |
| ADR-052 | 🏁🏁🏁 EL HAUPTSATZ — H3 cerrada, y la inducción doble que no hizo falta | ✅ ACEPTADA |
| ADR-053 | La consistencia de `Derives₀` SIN `Classical.choice` — y la no-constructividad estaba en el TIPO DE LLEGADA | ✅ ACEPTADA |
| ADR-054 | COMPACIDAD y LOEWENHEIM-SKOLEM DESCENDENTE — el patron del SUJETO, cobrado dos veces | ✅ ACEPTADA |
| ADR-055 | Herbrand para un BLOQUE de existenciales — la mitad ⟸ pagada, la ⟹ enunciada; y lo MEDIDO sobre LS ascendente | ✅ ACEPTADA |
| ADR-056 | H sobre F — y el axioma de Skolem/Henkin es CONSERVATIVO | ✅ ACEPTADA |
| ADR-057 | La CAPA PRENEXA sobre `Derives₀` — las ocho equivalencias, y la clásica no la pone Lean | ✅ ACEPTADA |
| ADR-058 | La FORMA NORMAL prenexa — y la «medida de terminación» que no hacia falta | ✅ ACEPTADA |
| ADR-059 | SKOLEMIZACION — el axioma con termino de argumentos fijos, y el bloqueo n-ario que NO existia | ✅ ACEPTADA |
| ADR-060 | SKOLEM bajo un PREFIJO de universales — el entorno no se RECONSTRUYE, se CONSTRUYE | ✅ ACEPTADA |
| ADR-061 | FOL adopta `check-doc-sync` -- y en su PRIMERA ejecucion encuentra NUEVE cosas | ✅ ACEPTADA |
| ADR-062 | 🏁 LA FORMA NORMAL DE SKOLEM -- y la recursion se pasa, no se mide | ✅ ACEPTADA |
| ADR-063 | 🏁 MAEHARA y la INTERPOLACION DE CRAIG para `LKp` -- y la condicion correcta no es la que uno escribe primero | ✅ ACEPTADA |
| ADR-064 | 🏁 La mitad ⟹ de HERBRAND DE BLOQUE -- y la funcion que ya llevaba el dato | ✅ ACEPTADA |
| ADR-065 | La direccion ⟹ de Skolem, `check-warnings.bash`, y el informe de PeanoRF MEDIDO | ✅ ACEPTADA |
| ADR-066 | El enchufe Skolem<->Herbrand, y la MEDICION del paso 4 (`String -> S`) | ✅ ACEPTADA (§1)  |
| ADR-067 | ⛔⛔ `maehara_eq` relativizado a `E` es VACUO -- y lo prueba un lema que yo escribi a favor | ⛔ RUTA DESCARTADA (con contraejemplo COMPILADO)  |
| ADR-068 | 🏁 el TIPO DE LOS SÍMBOLOS es un PARÁMETRO — y costó **3 ficheros**, no 163 | ✅ ATERRIZADO  |
| ADR-069 | 🏁 la CAPA DE OPERACIONES, genérica — y el orden que el panel corrigió | ✅ ATERRIZADO  |
| ADR-070 | ⛔⛔ M-10 **NO** puede entrar en la firma — y la clase resultó ser otra cosa | ⛔ IDEA DESCARTADA, con **caracterización exacta compilada**  |
| ADR-071 | 🏁 `Derives₀` genérico — **dos firmas** — y la obligación que yo inventé, REFUTADA | ✅ ATERRIZADO  |
| ADR-072 | 🔧 **A3 y A1** — dos controles que aprobaban siempre, rearmados y **probados rompiendo** | ✅ ATERRIZADO  |
| ADR-073 | 🔧 **A4 y A2** — certificar el par, y la definición de «TITULAR» que faltaba | ✅ ATERRIZADO  |
| ADR-074 | ✅ **⬜4** — sí hay linter en v4.31 sin Mathlib, y su punto ciego está MEDIDO | ✅ MEDIDO con evidencia compilada (`sondeos/lintlab/`)  |
| ADR-075 | 🏁 la ESTRUCTURA del caso (e) — y **dos afirmaciones falsas** en la cabecera que la describía | ✅ ATERRIZADO (§1bis de `ChainNegPrf`)  |
| ADR-076 | 🏁 la causa **(d)**, CERRADA de punta a punta — y la ✅ que la daba por cerrada era **falsa** | ✅ ATERRIZADO (4 ficheros)  |
| ADR-077 | 🏁 la causa **(e)**, CERRADA — y la que iba a ser cara salió de **refutar por instanciación** | ✅ ATERRIZADO (`ChainNegPrf` §2quater, 5 lemas)  |
| ADR-078 | 🏁 el **DESPACHADOR**, aterrizado — y el riesgo declarado de la vía **se cae al medirlo** | ✅ ATERRIZADO (`ChainNegPrf` §4, `dispatcher`, **net-0 puro**)  |
| ADR-079 | 🏁 la causa **(b)**, CERRADA — una tanda mecánica se ESCRIBE, no se cotiza | ✅ ATERRIZADO (`ChainNegPrf` §1ter: 19 ramas + `derives_lineWF_neg_of_a… |
| ADR-080 | 🏁 la causa **(c′)**, CERRADA — y **cinco de los siete lemas duros ya estaban escritos** | ✅ ATERRIZADO (`ChainNegPrf` §1quater: `TagCode` + cierre + los **19** … |
| ADR-081 | 🏁 la causa **(f)**, MEDIDA y con sus refutadores cerrados — y no era un muro | ✅ ATERRIZADO (`Meta/CodeDistinct.lean` + `ChainNegPrf` §1quinquies)  |
| ADR-082 | ⭐⭐⭐ la INVERSIÓN de `StdArgs` — un cambio de **SOPORTE**, no un lema | ✅ ATERRIZADO (`ChainNegPrf` §1ter)  |
| ADR-083 | 🏁 el MURO de `Model` — alcance **9 ficheros**, trabajo **1** | ✅ ATERRIZADO (`FOL/FOL/Semantics.lean`, commit `2d5b7c8`)  |
| ADR-084 | 🔧 la DEUDA DE CONTROL, adjudicada — y **las tres cifras publicadas estaban bajas** | ✅ ATERRIZADO (`check-doc-sync.bash`: `[H]` nuevo, `[E]` ampliado, `[B]… |
| ADR-085 | 📏 **M1–M4**: el modelo de los 141 es alcanzable — y el censo de agujeros sale **limpio** | ✅ MEDIDO (`sondeos/ModeloDiscriminador.lean`)  |
| ADR-086 | 🏗️ el MODELO ESTÁNDAR arranca — **8 de los 34 core**, y la raíz entera era lo único que faltaba | ✅ ATERRIZADO (`sondeos/ModeloNat.lean`)  |
| ADR-087 | 🏁 la capa ARITMÉTICA del modelo, COMPLETA — **25 de los 34**, y el molde no falló ni una vez | ✅ ATERRIZADO (`sondeos/ModeloNat.lean`)  |
| ADR-088 | ⛔⛔ **ℕ no es modelo de `Prf`** — la capa de listas se para antes de empezar | 📏 MEDIDO Y COMPILADO (`sondeos/ModeloBasura.lean`)  |
| ADR-089 | 🏁 EL REPARTO — **son SEIS ramas, no veintiuna** | ✅ ATERRIZADO (`ChainNegPrf` §5)  |
| ADR-090 | ⛔⛔ relativizar `listInd` **NO es barato** — toca los activos del núcleo | 📏 MEDIDO (censo con 8 agentes, **lectura**, no compilación)  |
| ADR-091 | ⭐⭐ los 21 tags sólo tienen **SEIS FORMAS** de argumentos | ✅ ATERRIZADO (`ChainNegPrf` §5, cuatro de las seis)  |
| ADR-092 | ⛔ el modelo de TÉRMINOS es **CIRCULAR** — y aparece una salida que no había | 📏 MEDIDO  |
| ADR-093 | ⭐⭐ **CÓMO se corrige la basura** — sacando el `σ` fuera, y está MEDIDO | 📏 MEDIDO Y COMPILADO (`sondeos/CantorSobreyectivo.lean`)  |
| ADR-094 | 🏁 **el cierre de UN tag, de punta a punta** — y el coste por tag queda MEDIDO | ✅ ATERRIZADO (`ChainNegPrf` §5, `cierra_tag0`)  |
| ADR-095 | 🏁 la forma `[F,F]` COMPLETA — un refutador para ~32 ranuras y un cierre por FORMA | ACEPTADO  |
| ADR-096 | 🏁 los DIECIOCHO tags estructurales, cerrados — y `NotTC`, la mitad que faltaba | ACEPTADO  |
| ADR-097 | 🏁🏁🏁🏁 `DEUDA_chainNeg` SALDADA y **`NegVerifier` PROBADO** | ACEPTADO  |
| ADR-098 | ⛔⛔ la propiedad de disyunción para `Derives₀` es **FALSA** — y la que se quería **ya estaba probada** | 📏 MEDIDO Y COMPILADO  |
| ADR-099 | 🏁 el CIERRE de FOL — (D)(B)(C), el encargo §3, la cuarentena vaciada y `folSystem` retirada | ✅ EJECUTADO  |
| ADR-100 | 🏁 el CIERRE de FOL, la tarde — seis teoremas, cuatro decisiones y una política de congelación POR FICHERO | ✅ EJECUTADO |
| ADR-101 | las decisiones D1-D7 del propietario sobre el cierre de FOL, y la condición para PeanoRF | 🔄 EN EJECUCIÓN (D1 hecho)  |
| ADR-102 | D2, D4, D5, D6 y D7 ejecutadas — y la regla de subíndices de cálculo, también en RPP (`Prf₀` → `Prfᵢ`) | ✅ EJECUTADO (D3 aplazada por el propietario)  |
| ADR-103 | D3 CERRADA — Craig para `Derives₀` CON igualdad, y Herbrand para `φ` y `Γ` cualesquiera | ✅ EJECUTADO  |
| ADR-104 | `Prf` sin subíndice; la documentación de FOL al día; y la criba de congelación con refutación | ✅ EJECUTADO; ⬜ el `freeze` espera la confirmación del propietario  |
| ADR-105 | 🧊 los cinco primeros módulos de FOL CONGELADOS; P2 (18 renombres) y P3 (los `sub_*`) | ✅ EJECUTADO; ⬜ P4 en cotización  |
| ADR-106 | P4 cotizada — la versión ACOTADA de `derives0_qf_iff`, y el decisor del fragmento sin cuantificadores | 📐 COTIZADA; ⬜ decisión del propietario  |
| ADR-107 | P4 hecha — `FOL/QFDecide0.lean`: el fragmento sin cuantificadores de `Derives₀`, ACOTADO y DECIDIDO | ✅ HECHA  |
| ADR-108 | La segunda criba de congelación de FOL — 71 correcciones, 10 congelables propuestos, decisiones N1‑N4 | ✅ criba hecha; ⬜ freeze y N1‑N4, del propietario  |
| ADR-109 | N1‑N4 de FOL resueltas — 13 renombres, dos duplicados retirados; los 10 congelables, sólo bloqueados | ✅ HECHA  |
| ADR-110 | La auditoría de constructividad de FOL y D1‑D8 — `Classical.choice` 157 → 84, y la LOCALIZACIÓN del WKL (ADR-040 §2, ADR-041 §4), refutada | ✅ HECHA  |
| ADR-111 | La tercera criba de congelación de FOL, tras D1‑D8 — 10 congelables propuestos; N6 aplicada; N5 y N7 al propietario | ✅ criba hecha; ⬜ freeze, N5 y N7, del propietario  |
| ADR-112 | FOL — el segundo y el tercer lote CONGELADOS (23 módulos); N5, auxiliares; N7, el enunciado de `herbrand_of_skolemNF₀` reforzado | ✅ HECHA  |
| ADR-113 | 🏁 la salida (5) ADOPTADA — `cons a b = σ (pair a b)`, y el radio medido por el compilador | ✅ HECHA (rama `claude/project-thread-bgzgkr`)  |
| ADR-114 | 🚨 la auditoría de la BASE, ronda 1 — cuatro defectos COMPILADOS, y las cuatro decisiones del propietario | ✅ decisiones 1, 3 y 4 ejecutadas; ✅ la 2, en RPP ([ADR-115](#adr-115))… |
| ADR-115 | 🗑️ la capa `⊢` RETIRADA de RPP — 27 módulos, 633 declaraciones, 0 `axiom` de Lean, y la cadena sobre `Prf` intacta | ✅ RPP (`b1dedd1`)  |
| ADR-116 | 🔧 los controles que daban verde sin comprobar — `[B]` por prefijo, `check-axioms` por grep, `check-estratos` sin `TheoryFramework` ni `private` —, cuatro revisiones adversariales de los arreglos, y el `thaw` de los cinco congelados de FOL | ✅ RPP (este commit, tras `57ad71f`: §8)  |
| ADR-117 | 🏁 F1 reparado — `axiomsCodeT` anclado por un axioma DIAGONAL; `AnclaEq` pasa a ser TEOREMA, y Gödel I/II dependen sólo de `ConsistentH` | ✅ (este commit)  |
| ADR-118 | 🗑️ la clase `AnclaEq` RETIRADA — 426 ligaduras, un commit mecánico | ✅ (este commit)  |
| ADR-119 | 🏁 el MODELO de los 142 — `ConsistentH` DEMOSTRADA, en `sondeos/ModeloNat.lean` | ✅ (este commit; un SONDEO, fuera del build)  |
| ADR-120 | 🏁🏁 `ConsistentH` es un TEOREMA del build — Gödel I y II SIN HIPÓTESIS | ✅ (este commit)  |
| ADR-121 | 🏁🏁 GÖDEL I ENTERO (`⊬ ¬G`, por W1) y TARSKI, sin hipótesis | ✅ (este commit; arregla además el rojo de la CI de ADR‑120: [E] de |
| ADR-122 | 📏 D7 MEDIDA —la puerta contrafactual dice NO— y Rosser re‑medido tras el modelo | ✅ medición (este commit; ⬜ la decisión sobre D7 es del propietario)  |
| ADR-123 | 🔬 Rosser, Etapa 0 — la REFLEXIÓN numeral de `substfc`/`liftfc`, CONFIRMADA (sondeo) | ✅ sondeo (este commit)  |
| ADR-124 | ⛔ El CONTROL NEGATIVO del modelo, en el build — y la auditoría de ADR‑123 | ✅ (este commit)  |
| ADR-125 | 🔬 Rosser, Etapa 0, segunda pieza — la guarda de término REFUTADA sobre un NUMERAL (sondeo) | ✅ sondeo (este commit)  |
| ADR-126 | 🔬 Rosser, Etapa 0 — un caso HEREDITARIO (la basura en la lista de argumentos), y un control (sondeo) | ✅ sondeo (este commit)  |
| ADR-127 | 🔎 La auditoría de ADR‑124/125/126 —y los 88 sondeos, re‑medidos | ✅ (este commit)  |
| ADR-128 | ⚙️ `autoImplicit` desactivado también en `lake build` —en RPP y en FOL—, sin coste medido | ✅ (este commit; FOL `1df51b3`)  |
| ADR-129 | 🔤 D7 EJECUTADA — los símbolos de FOL son `List Char`, en FOL y en RPP | ✅ (este commit; FOL `14b1692` y el re‑freeze `f53953f`)  |
| ADR-130 | 🔬 Las dos notas de `CodeDecode`, MEDIDAS — el `if` sobre un símbolo no es frágil en el núcleo; lo es desplegar por defeq una recursión MUTUA | ✅ medición (este commit)  |

## Plantilla para nuevas decisiones

## ADR-131: 📏 De dónde viene el `Classical.choice` de los titulares — NO de `p3`: dos cancelaciones de lift lo traen a 158 de 182 filas

**Fecha:** 2026-10-05 · **Estado:** ✅ medición y fe de erratas (este commit) · **Ámbito:** `sondeos/ChoiceFrontera.lean`
(nuevo: lee el entorno, no evalúa nada del lenguaje objeto); notas fechadas en ADR‑129 §2, el banner de `REFERENCE.md`
y `doc/PLAN-COMPLETITUD-FINITISTA.md` §7.3. Origen: la auditoría del suelo (`wf_1f61bc0d-738`), que la marcó.

### 1 · Lo que ADR‑129 dijo

«NO lo pierden los titulares de Gödel, la solidez ni Tarski: su `choice` es el de la solidez clásica (`prf_sound`,
el axioma `p3`)». Era una INFERENCIA escrita como hecho, repetida en el banner de `REFERENCE.md`, en el plan y en el
informe al propietario.

### 2 · Lo medido

La FRONTERA de un titular: las constantes del proyecto (también las `private`) de su cierre de dependencias que
nombran DIRECTAMENTE una constante ajena cuyo cierre contiene `Classical.choice`. Por ahí entra.

| titular | puntos de entrada |
|---|---|
| `goedel_first_prf`, `prf_tarski` | sólo `SubstArith.substTerm_liftLiftLift` (`Classical.byContradiction`) |
| `goedel_second_prf` | `substTerm_liftLiftLift` y `substTerm_liftLiftLiftLift` |
| `prf_sound` | ella misma: el caso `p3` (`Classical.byContradiction`) |
| `consistencia` | `prf_sound` y `ModeloEstandar.v_ax16` (`Classical.propDecidable`) |
| `goedel_I`, `tarski` | `prf_sound`, `v_ax16` y `substTerm_liftLiftLift` |
| `goedel_II` | los de `goedel_I` y `substTerm_liftLiftLiftLift` |
| `goedel_I_neg` | los de `goedel_I` y su propia prueba (`Classical.byContradiction`) |

Censo sobre las 182 filas de RPP de `check-footprints` que declaran `Classical.choice` (117 s): pasan por
`prf_sound`, **14**; por `substTerm_liftLiftLift`, **169**; por `…LiftLiftLift`, **126**; por `v_ax16`, 14; el resto,
4 o menos cada uno (los round‑trips de `CodeDecode`, `ChainDecode`, `ChainNegPrf`). **158** tienen TODA su frontera en
las dos cancelaciones de lift.

### 3 · Veredicto

La frase de ADR‑129 es falsa para las 168 filas que no pasan por `prf_sound`, entre ellas `goedel_first_prf`,
`goedel_second_prf` y `prf_tarski`; y en `goedel_I`, `goedel_II`, `consistencia` y `tarski`, `prf_sound` es uno de dos
a cuatro puntos de entrada. Lo cierto de ADR‑129: ya no entra ningún `choice` por `String` (`D7Contrafactual`).

### 4 · Lo que NO dice

* «158» es el contrafactual de CORTAR esas dos constantes, como `D7Contrafactual` cortaba `String.*`: cuántas filas
  perderían `choice` si las dos cancelaciones se probaran sin él. Es una cota INFERIDA: no se ha reescrito ninguna
  prueba, y reescribirlas podría meterlo por otro sitio. ⬜ Medirlo es reescribirlas (sus `omega`/`by_cases`/`simp`).
* No se ha medido qué táctica de esas dos pruebas trae `Classical.byContradiction`.
* Las 14 que pasan por `prf_sound` lo conservarán mientras la semántica sea en `Prop`: validar `p3` (la doble
  negación) pide tercio excluso (INFERIDO). `v_ax16` (`Classical.propDecidable`) no se ha mirado.

🔑 *La causa de un footprint se MIDE en la frontera de su cierre; no se deduce del lema que parece más clásico.*

**Véase también:** ADR‑129 (la frase corregida), ADR‑122 (`D7Contrafactual`, el mismo método con `String`).

---

<a id="adr-132"></a>
## ADR-132: 📋 La auditoría del suelo, versionada —81 trabajos priorizados— y T00: los artefactos que vivían fuera de git, rescatados

**Fecha:** 2026-10-12 · **Estado:** ✅ (este commit) · **Ámbito:** `doc/AUDITORIA-SUELO-2026-10-12.md` y `doc/registro/`
(nuevos), `scripts/pruebas/`, `scripts/sondeos_todos.ps1`, `sondeos/pasadas/`, `sondeos/D3Sigma1Vacuo.lean` (nuevo),
`.gitignore`, banners (91 sondeos). Ninguna línea del build cambia.

### 1 · La auditoría

El propietario preguntó el 2026‑10‑05 qué trabajos quedan «sin dejar pasar cuestiones de medida, de fundamentos, tareas
underground… que dejen un suelo muy firme». Dos workflows de sólo lectura: `wf_1f61bc0d-738` (2026‑10‑05: seis barridos
y seis verificadores; 162 candidatos vivos) y `wf_7a6e4ce2-b37` (2026‑10‑12: agrupar, crítico de completitud, cinco
verificadores adversariales sobre los P0/P1 y síntesis). Resultado: **81 trabajos**, con su evidencia y cómo cerrar
cada uno, en `doc/AUDITORIA-SUELO-2026-10-12.md`:

* **P0 (4)**: T01, Rosser con un enunciado con contenido antes de pagarlo (con `ConsistentH` teorema, todo
  `rosser (hcon : ConsistentH)` sobre T fija es trivial); T02, la teoría `T_Prf` descrita con precisión (README dice «sin
  esquema de inducción» y `Prf` tiene inducción completa); T03, la tabla MANDATORIES (M‑11 al revés, M‑10 y M‑6 falsas);
  T04, el núcleo de `[B]` (absuelve citas muertas por subcadena).
* **P1 (7)**: T00 (éste), T04b, T06 (sondeos en la CI con las opciones del build), T07 (contrato de enunciados), T08
  (control de pureza del cierre), T09 (TEOREMAS‑E‑HIPOTESIS) y T15 (todo `.lean` en el build).
* **P2 (51)** y **P3 (19)**; **21 decisiones del propietario**. La segunda verificación sólo cubrió T01–T23 y CRI‑01…03.

### 2 · Medido el 2026‑10‑12

* **T05**: `sondeos/D3Sigma1Vacuo.lean` compila (entre 4 y 76 s en tres ejecuciones) y refuta `hI` y `hbI` con el modelo:
  `d3_prf_of_sigma1` y `d3_prf_of_reflect_bounded` (`Meta/ReflectionPrf.lean`, `Meta/Sigma1BoundedPrf.lean`) son VACUOS.
  Ninguno tiene consumidor; el D3 que se usa, `d3_prf_real`, no lo es. ⬜ Retirarlos o marcarlos.
* **T11b**: `#print axioms` de `repr_pos'_prf` y `prf_con_imp_godel`, `[propext, Classical.choice, Quot.sound]`; de
  `d2_prf` y `prfI_sound`, `[propext, Quot.sound]`. ⬜ Darles fila en `check-footprints.bash`.

### 3 · T00: lo rescatado

`doc/registro/README.md` es el índice: las rondas 1 y 2 de la auditoría de la base (2026‑10‑02), la medición de D7 y el
plan de Rosser (ADR‑122), las auditorías de ADR‑121, ADR‑123…125 y ADR‑124…126, la exploración de D7 y la revisión de su
prosa (ADR‑129), y los registros de esta auditoría; fuera de `doc/`, el runner de los sondeos y sus tablas
(`scripts/sondeos_todos.ps1`, `sondeos/pasadas/`), la réplica de `[B]` (`scripts/pruebas/b/`) y las herramientas que
validaron `strip-lean.awk` (`scripts/pruebas/`). Las rutas locales absolutas, saneadas; las sondas del registro, como
`.lean.txt`; omitido `parsed.json` (4,3 MB, regenerable). ⚠️ Los scripts de `scripts/pruebas/strip-lean/` apuntan todavía
al temporal de la sesión: hacerlos ejecutables desde aquí es T47.

ADR‑129 decía «revisión adversarial aplicada» sin decir cuál: ahora la cita (T17, en parte).

### 4 · Lo que NO dice

* Los 81 trabajos son los hallazgos de los agentes, con sus etiquetas; T24–T74 no tuvieron segunda verificación.
* Ninguna de las 21 decisiones está tomada: T01 (Rosser) sigue abierta, y es la que desbloquea más.
* El registro es REGISTRO: lo que diga sobre el código es de su fecha.

🔑 *Una auditoría que no se versiona se audita dos veces: ésta redescubrió al menos siete hallazgos de las rondas 1 y 2,
que vivían fuera de git.*

**Véase también:** ADR‑114/115 (la auditoría de la base), ADR‑129 (D7), ADR‑131 (la frontera del `choice`).

---

<a id="adr-133"></a>
## ADR-133: 📜 La tabla MANDATORIES, corregida —M‑11 al derecho, M‑10 y M‑6— y el control [M]

**Fecha:** 2026-10-12 · **Estado:** ✅ (este commit) · **Ámbito:** `DECISIONS.md` (MANDATORIES: M‑6, M‑10, M‑11 y la
verificación de M‑7 y M‑13; notas fechadas en ADR‑025, ADR‑026, ADR‑029 §2 y ADR‑038 §3), `check-doc-sync.bash` (el bloque
`[M]`, nuevo, y su cabecera), `Meta/Representability2Prf.lean` (un comentario), `.github/workflows/build.yml` y `Makefile`
(comentarios), `doc/PLAN-COMPLETITUD-FINITISTA.md`; y la memoria de los dos chats. Es T03 (P0) de
`doc/AUDITORIA-SUELO-2026-10-12.md`.

### 1 · Lo que decía la tabla de lectura obligatoria

`AI-GUIDE.md` obliga a leer MANDATORIES antes de tocar un `.lean`. Diez días después de ADR‑114 seguía enseñando:

* **M‑11**, al revés: «antes de demostrar algo por INDUCCIÓN… comprobar que NINGÚN `axiom` lo habita… ⇒ el teorema es
  FALSO», «`Derives` NO ADMITIRÁ INDUCCIÓN NUNCA», con las listas negra y blanca de septiembre (`Prf₀`, `prf0_soundness`…).
  ADR‑114 §2 lo había invertido, y el build hace lo contrario: induce sobre `Derives` (`derives_to_derives0`) y sobre
  `Prf` (`prf_sound`, en la que descansa `ConsistentH`).
* **M‑10**, verificada con `derives_completo` y `hgi_es_refutar`, sin declaración desde ADR‑115, y apoyada en
  `Meta/OmegaStrength.lean`, borrado en `b1dedd1`.
* **M‑6**: «`[A]`, `[C]` y `[D]` rompen; `[B]` es aviso». `[B]` rompe desde ADR‑084.
* Y de paso: **M‑13** decía «⬜ falta `check-warnings.bash`», que existe desde ADR‑065; **M‑7** citaba en su
  verificación `hPl`, una hipótesis, no una declaración; **M‑1** verificaba con `grep '^axiom '`, sustituido en ADR‑116.

### 2 · Lo que dice ahora

* **M‑11**: antes de POSTULAR un `axiom` que habita un inductivo, comprobar que no contradice lo que se demuestra por
  inducción sobre él; la inducción es válida, lo que puede ser falso es el axioma. La regla de diseño (una regla nueva de
  una relación inductiva va como CONSTRUCTOR, nunca como `axiom`) sigue. Verificación: `check-estratos.bash`.
* **M‑10**: los enunciados de indemostrabilidad, indecidibilidad o consistencia van sobre `Prf`. Verificación: las filas
  de `goedel_I`, `goedel_I_neg`, `goedel_II` y `goedel_second_prf`; que el ENUNCIADO hable de `Prf`, lo fijará T07.
* **M‑6**: rompen `[A]`, `[B]`, `[C]`, `[D]`, `[E]`, `[F]`, `[H]` y `[M]`; sólo `[A2]` avisa; y se lanza desde PowerShell.
* Cada fila corregida lleva su ✏️ con lo que decía. Las copias de la doctrina vieja llevan la suya: ADR‑025, ADR‑026,
  ADR‑029 §2, ADR‑038 §3, `Meta/Representability2Prf.lean`, `build.yml`, `Makefile`, la cabecera de `check-doc-sync.bash`
  y PLAN‑COMPLETITUD; y la memoria de RPP y la del chat de FOL, que repetían M‑11 vieja o la premisa de M‑10.

### 3 · El control `[M]`

Cada fila de la tabla debe ocupar UNA línea con 4 columnas (la M‑11 vieja, partida en dieciséis, escondía así su
verificación). En la columna «Verificación», cada cita entre comillas invertidas se comprueba según su forma: una
ruta, que exista; un nombre, que esté DECLARADO en el build, en FOL o en un sondeo (las listas de `[B]`); una orden,
por sus rutas y por sus palabras con forma de nombre Lean con `_` (las de un patrón entrecomillado no cuentan; con `_`
final, como familia); un sufijo como `_rhs`, con la cita anterior de su fila; un módulo, por su fichero. Sólo tres
palabras clave de Lean (`axiom`, `export`, `rfl`) quedan fuera, y ningún marcador absuelve. Lleva un autotest (dos
filas sintéticas: tres citas muertas, una viva que sólo declara un sondeo, y una fila partida, deben dar 4 fallos) y
se niega a medir con menos de 10 filas o 20 citas. Con `M_DOC=` lee otra tabla en MODO DE PRUEBA, que nunca da verde.

**Se estrenó con el fallo puesto** (MEDIDO, con `M_DOC=` la tabla de antes de este ADR): ROJO con la fila M‑11
partida, `hPl` en M‑7, y `derives_completo` y `hgi_es_refutar` en M‑10. Sobre una tabla de prueba con los casos de la
revisión (una fila partida, un `|` dentro de una cita, nombres muertos dentro de una orden y de una lista, una fila con
guion no separable, un sufijo sin nombre delante), ROJO en los nueve; el nombre que sólo declara un sondeo y la familia
`ax_tc_`, en verde. Sobre la tabla de hoy: 33 citas en 13 filas, todas existen.

La revisión adversarial de esta pasada (un agente, sólo lectura) encontró doce defectos, todos aplicados antes del
commit: cuatro de `[M]` que daban verde sin comprobar (la fila partida, la rama de las órdenes, un `|` dentro de una
cita, una fila con guion no separable) o rojo falso (`pipefail` cortaba la búsqueda en los sondeos), y ocho de texto.

### 4 · Lo que NO dice

* `[M]` comprueba que lo citado EXISTE, no que la verificación verifique la regla; y sólo mira lo que va entre comillas
  invertidas.
* M‑3 (T16) y M‑5 (T35) no se tocan: esperan su propio trabajo. `AI-GUIDE.md` §27 y la receta `/docsync` siguen dando
  `[B]` y `[E]` por avisos y no nombran `[M]`: es T21. La copia de FOL (`../FOL/FOL/Derives0.lean:181-182`) espera a un
  commit de FOL; las filas del catálogo de sondeos y sus docstrings, registro, llevan una línea fechada en
  `sondeos/README.md`.
* Los ADR históricos conservan su texto; la nota fechada de arriba lo marca.

🔑 *Una regla obligatoria que nadie verifica se pudre como cualquier texto: la tabla que todo agente lee antes de tocar
un `.lean` enseñaba M‑11 al revés diez días después de corregirla.*

**Véase también:** ADR‑114 §2 (M‑11, invertida), ADR‑115 (la capa `⊢`, retirada), ADR‑132 (la auditoría).

## ADR-134: 📐 La teoría de los titulares, descrita —`T_Prf` contiene a PA— y lo que se supone hoy; D1 usa la inducción

**Fecha:** 2026-10-14 (empezado el 2026‑10‑12) · **Estado:** ✅ (este commit) · **Ámbito:** `AXIOMS.md` (§0, nueva, la
descripción canónica; notas fechadas en la introducción, §1.1 y §4), `README.md`, `GODEL-STATUS.md` (l.74 y §1), y notas
fechadas o avisos de vigencia en otros dieciocho documentos (los de la tabla de §5); comentarios de 113 ficheros
`.lean` (72 del build, con la raíz, y 41 de `sondeos/`); `sondeos/InduccionTitulares.lean`, nuevo; y `doc/registro/2026-10-12-t02-teoria/`, la evidencia. Es T02 (P0)
de `doc/AUDITORIA-SUELO-2026-10-12.md`, con README:108 (T25) y GODEL-STATUS.md:74 (T28); y, por orden del propietario
del 2026‑10‑14 («arreglar todos los comentarios erróneos o que haya que poner al día»), los comentarios desactualizados
que encontraron los censos aunque no fueran de la teoría: T31 entero, y parte de T05, T10, T27, T29, T30 y T32. Ningún
enunciado ni ninguna definición cambia: en los `.lean`, sólo comentarios (MEDIDO: despojados de comentarios con
`strip-lean.awk`, los 113 dan el mismo código que en `HEAD`, salvo líneas en blanco).

### 1 · Lo que decían los documentos

La teoría de la que hablan los titulares estaba mal descrita donde más se lee, y de tres maneras incompatibles:
* **«Q++: aritmética de Robinson extendida, sin esquema de inducción»** (README, la tabla de capas; `REFERENCE.md` y
  `doc/REFERENCE-Kernel.md`, «teoría objeto FOL⁼ (Q++)») y «34 axiomas sin un esquema de inducción general» (README).
* **«IΣ₁»** (`Minimal/Axioms.lean`, en el comentario de `ax_vpf_ind`; `AXIOMS.md` §1.1, «Q++ + inducción (perfil IΣ₁)»;
  `NEXT-STEPS.md`, «`provCodeC` rastrea IΣ₁»; `GODEL-D-ARITHMETIZATION.md`, D‑4).
* **«extensión definicional conservadora»** (`Minimal/Axioms.lean`, tres sitios; `AXIOMS.md`, «Anclas»;
  `doc/REFERENCE-Incompleteness.md`; `NEXT-STEPS.md`; `CURRENT-STATUS-PROJECT.md`), nunca probada. Y `MINIMAL-AXIOMS.md`
  decía que `Minimal` es «un fortalecimiento conservativo de Q», lo que es falso en cualquier fecha: `ax6` está en el
  lenguaje de Q y Q no lo demuestra.
Ningún documento vigente enunciaba la teoría entera.

### 2 · Lo que es

`T_Prf`, lo que deriva `Prf` (`Meta/Hilbert.lean`): en el lenguaje de TODAS las `Formula` de FOL —cualquier símbolo,
cualquier aridad; los 142 axiomas nombran 33 símbolos, 28 de función y 5 de relación—, los 142 axiomas de `axioms` por
`thy`, los esquemas lógicos de `Prfᵢ` con DNE (`p3`) y el confinamiento (`qconf`), y la inducción (`ind`) y la de listas
(`listInd`) para TODA fórmula, con MP y GEN. Por lectura, **contiene a PA**: `ax2`, `ax3`, `ax4`, `ax5`, `ax8` y `ax9`
son los seis axiomas de Peano de primer orden, la inducción no tiene restricción, y el cálculo lógico es un Hilbert
clásico estándar (que sea completo no está demostrado: es la dirección `DerivesSet₀ → Prf` de T67). No es Q, ni Q++ sin
inducción, ni IΣ₁. Lo que no tiene esquema de inducción es la LISTA `axioms`, que ya contiene a Q (el Q3 de Robinson
sale sin inducción de `ax2`, `ax5`, `ax13` y `ax19`) y no es «≈ Q»: tiene además la conmutatividad, la asociatividad,
la distributividad y el orden. Va, canónica, en `AXIOMS.md` §0, con:
* **lo que no se sabe**: que sea conservativa sobre PA (lo esperable por el argumento estándar, pero no está hecho; y
  ADR‑054 §4 descartó el metateorema general porque `ax_tc_cons`, retirado en ADR‑012, había dado `axioms ⊢ ⊥`); que
  la codificación tampoco es «definicional»: las ecuaciones de `substtc`, `liftc`, `substfc`, `liftfc`, `carc`, `cdrc`,
  `nthc`, `premsOf`, `validProofFn` y la resta no fijan el valor fuera de la forma prevista (una especificación
  PARCIAL); si `listInd` se deriva de `ind` (lo esperable, porque `σ ∘ pair` es biyectiva desde ADR‑113; no basta
  `t < h :: t`); la traducción a {0, σ, +, ×}; y el puente con `DerivesSet₀` (T67): `goedel_I` dice que ESTE cálculo no
  deriva `G`;
* **lo que se supone hoy**: el núcleo de Lean y sus tres axiomas, y nada sobre la teoría, cuya verdad está DEMOSTRADA
  (`MN_axioms` para los 142; `prf_sound` para los esquemas, en todo modelo `Estandar` —dominio ℕ, 0 y σ los de siempre,
  `::` el `consN` de ADR‑113, y los 142 verdaderos—; no hay solidez respecto de TODO modelo); y las definiciones, que no
  fija ningún control (T07).

### 3 · Medido: dónde entra la inducción

`AXIOMS.md` §1.1 decía «D1 y D2 no usan la inducción, verificado con `#print axioms`». Se midió sobre los `axiom` de `⊢`;
sobre `Prf`, `#print axioms` no puede verlo, porque `ind` y `listInd` son constructores. `sondeos/InduccionTitulares.lean`
(nuevo, ≈ 20 s) recorre el cierre de dependencias de cada titular y lista las constantes cuyo VALOR nombra un constructor
de la regla, en las tres representaciones de una derivación (`Prf`, `PrfH`, `HilbertSeq.Rule`); separa las cuatro
traducciones entre ellas, y el resto se clasificó leyendo el fuente. `#camino` da un camino por valores y `#usuarios`, los
usuarios directos. Resultado (MEDIDO el 2026‑10‑12; re‑ejecutado el 2026‑10‑14 sobre el build de ese día, con el mismo
resultado y `tarski` y `tarski_semantico` añadidos):
* D1 (`repr_pos'_prf`) **usa la inducción**: su término de prueba alcanza `prf_nat_induction` (`Prf.ind` y dos MP) por
  `prf_zero_or_succ` (Q3), `prf_add_zero_left` (0 + n = n, por el ancla diagonal: 18 aristas), `prf_add_succ_left` y
  `prf_mul_le_mono_right`. No usa la de listas. **Por lectura, los cuatro usos son evitables** (`0 + n = n` y
  `σm + n = σ(m + n)`, de `ax6` con `ax4` o `ax5`; Q3, de `ax2`, `ax5`, `ax13` y `ax19`; la monotonía, de `ax13`, `ax10`,
  `ax12`, Q3 y `ax4`); los comentarios de `NatArithPrf`, `NatOrderPrf` y `NatMulPrf` que decían otra cosa eran falsos,
  corregidos. Que D1 compile sin `ind` no está comprobado.
* D2 (`d2_prf`) usa la **de listas** (`prf_list_induction`, por `prf_runFn_concat` y otros ocho de `ChainPrf`) y no la
  aritmética: `prf_nat_induction` no está en su cierre.
* D3, `goedel_second_prf`, `goedel_II` y `prf_con_imp_godel` usan las dos; `goedel_first_prf`, `goedel_I`, `prf_tarski`,
  `tarski`, `tarski_semantico` y `goedel_I_neg`, la aritmética.
* **DNE**: ningún titular construye un paso `p3` salvo `goedel_I_neg`, que lo hace al decodificar con `linea_p3` las
  líneas que el verificador acepta en el modelo; en los demás sólo lo nombran las traducciones y los análisis por casos.
* `qconf` no se da por titular: lo construyen el caso `gen` del teorema de deducción (`deduction_aux`) y lemas de siete
  módulos.
* `prf_sound` y `consistencia`: frontera vacía para las cuatro reglas (analizan `Prf`; no construyen).
⚠️ «Usa» quiere decir que el término de prueba la nombra por valores; otra prueba podría evitarlo. La primera versión del
sondeo recorría los términos como ÁRBOL, sin memoria, para no contar los tipos de los ligadores, y no acababa: con la
compartición de los términos de prueba es exponencial. `getUsedConstants` recorre el grafo con memoria.

### 4 · La literatura: el párrafo de `AXIOMS.md` §1.1, frase a frase

Decía que «Gödel II sobre Q sin inducción» «es un enunciado falso». Es al revés (por la literatura, no medido aquí):
`Q ⊬ Con_Q` es un teorema para la formalización canónica —ninguna teoría r.e. consistente que interprete Q demuestra su
propia consistencia (P. Pudlák, «Cuts, consistency statements and interpretations», *JSL* 50, 1985, 423–441)—, y
A. Bezboruah y J. C. Shepherdson lo probaron directamente para una formalización natural («Gödel's second incompleteness
theorem for Q», *JSL* 41, 1976, 503–512, DOI 10.2307/2272251). Lo demás del párrafo era inexacto: para el predicado de
prueba sin relativizar no se sabe probar D3 en Q, pero relativizado a un corte definible en el que Q interpreta S¹₂ la
vía de Hilbert–Bernays–Löb llega a Q (S. R. Buss, *Handbook of Proof Theory*, 1998, §2.1.4 y §2.2.3); D1–D3 son
condiciones suficientes, y hay otros conjuntos suficientes, cada uno para su enunciado de consistencia (R. G. Jeroslow,
*JSL* 38, 1973, 359–367); e IΣ₁ es la base habitual de los manuales (P. Hájek y P. Pudlák, *Metamathematics of
First‑Order Arithmetic*, 1993, III.2.17 y III.2.22), no el mínimo: basta EA, y con una aritmetización eficiente, S¹₂
(Buss 1998, §2.1). El título de §1.1 («la inducción es imprescindible») no está justificado: no lo es para el teorema, y
para la vía de este proyecto, con el predicado sin relativizar, es una cuestión abierta. La nota va en §1.1, con la
numeración del proyecto (D1 necesitación, D2 distribución, D3 `Pr φ → Pr Pr φ`), que no es la de todos los autores.

### 5 · Lo demás que se tocó

| Documento | Qué cambió |
|---|---|
| `README.md` | la tabla de capas (la LISTA, sin esquema de inducción; la teoría, `T_Prf`), un párrafo sobre `T_Prf`, `⊬¬G` cerrada desde ADR‑121, «hasta ADR‑120 eran CONDICIONALES», «hay prueba de consistencia» y la línea de los `axiom` (0 en el build; `sondeos/` guarda cuatro) |
| `GODEL-STATUS.md` | la cabecera (su «Resumen al día» es registro) y una nota en §1 (el sujeto de los titulares es `T_Prf`) |
| `NEXT-STEPS.md` | el PUNTO DE REANUDACIÓN, la nota de julio (cuatro frases falsas hoy) y dos avisos de registro |
| `CURRENT-STATUS-PROJECT.md` | un aviso: desde el Resumen ejecutivo es registro del 2026‑09‑10 (se reescribirá, T26) |
| `REFERENCE.md`, `doc/REFERENCE-Kernel.md` | «Q++» fuera; el «Hoy» del 2026‑10‑04 y `⊬¬G`, registro; la fila de `ax_L0_cons_def` |
| `doc/REFERENCE-Incompleteness.md` | la firma de `Prf` con la inducción, `0 + n = n` sin inducción, el banner como registro, y §3.19: `d3_prf_of_sigma1` y `d3_prf_of_reflect_bounded`, VACUOS (T05) |
| `MINIMAL-AXIOMS.md` | aviso de vigencia; «fortalecimiento conservativo de Q» (falso en cualquier fecha) y la cadena de la jerarquía |
| `TuplasFuncionesYListas.md`, `ESCALANDO_EL_PROYECTO.md`, `GODEL-D-ARITHMETIZATION.md` | avisos de vigencia |
| `DEPENDENCIES.md`, `PLANNING.md`, `PLAN-PRUEBAS.md`, `PLAN-SORTES.md`, `NAMING-CONVENTIONS.md`, `doc/FEEDBACK-PARA-EL-LIBRO.md`, `DECISIONS.md` (la nota de ADR‑010) | notas fechadas: las meta‑reglas retiradas, P‑4, la inconsistencia de ADR‑012, la consistencia |
| `sondeos/README.md` | la fila del sondeo nuevo, la de `D3Sigma1Vacuo`, la de `ModeloNat` y una nota sobre las cabeceras viejas |
| `doc/AUDITORIA-SUELO-2026-10-12.md` | el estado de T02 y T31 (hechos) y lo que tocó de T05, T10, T25, T27, T28, T29 y T32 |
| los `.lean` (72 del build, con la raíz, y 41 de `sondeos/`) | §6: la teoría donde se describía; y el lote de comentarios caducados o falsos |

### 6 · Cómo se hizo, y la revisión

* **Los hechos y los censos** (2026‑10‑12): un workflow de doce agentes de sólo lectura, `wf_54bdca87-06c`: seis barridos
  (los 142 y el lenguaje; `Prf`, el modelo y la solidez; los titulares y lo que suponen; la literatura, con búsqueda web;
  y dos censos de cómo describen la teoría los `.md` y los `.lean`) y un verificador adversarial por cada uno. Los censos
  encontraron 180 apariciones (122 en los `.md`, 58 en los `.lean`; 22 FALSO‑VIGENTE, 46 HISTÓRICO‑SIN‑MARCA, 7
  DUDOSO). Los dos verificadores de los censos murieron por el límite de sesión.
* **La revisión adversarial** del 2026‑10‑13 (`wf_22f6795d-314`, cuatro agentes) murió entera por el mismo límite; uno
  dejó dos defectos en su transcripción, aplicados.
* **El 2026‑10‑14**, cinco agentes sueltos: tres revisores (hechos de código, matemáticas y literatura, coherencia y
  alcance) y los dos verificadores de los censos. Sus hallazgos se aplicaron todos, salvo los que se dicen en §7. Lo más serio: la vía de Hilbert–Bernays–Löb SÍ llega a Q relativizada (Buss), y la nota decía lo contrario; los
  cuatro usos de inducción de D1 son evitables, no tres; `listInd` no se deriva sólo de `t < h :: t`; `prf_zero_or_succ`
  es un axioma de Q, y una fila lo daba por «hecho que Q no demuestra»; `goedel_I_neg` sí construye pasos `p3`; y la
  firma de `Prf` de `doc/REFERENCE-Incompleteness.md` no tenía la inducción.
* **Los comentarios de los `.lean`** (2026‑10‑14, por orden del propietario). El verificador del censo de los `.lean`
  halló que de los 20 hallazgos falsos o dudosos del censo seguían 11 sin arreglar, y unas 180 omisiones. Lo que más se
  escapaba era el ESTADO del proyecto: C3 y D3 dados por pendientes en unos veinte módulos, ocho `export` con «nada lo
  consume», la ruta `hI`/`hbI` presentada como reducción cuando es vacua, unos quince nombres que no existen citados
  como vigentes y la deuda B6b dada por abierta. Y dos errores de contenido: la fórmula de Cantor de
  `Minimal/Axioms.lean`, que dividía dos veces, y la de `consN` de `Meta/CodeNatInjPrf.lean`, la de antes de ADR‑113.
  Siete agentes, sobre ficheros disjuntos, comprobaron cada hallazgo contra el fuente: corrigieron o anotaron 173, dos
  no hacían falta (ya los cubría una marca), ninguno resultó falso, y añadieron 16 que encontraron al leer. Tres
  revisores adversariales del lote comprobaron unas 485 afirmaciones nuevas y encontraron 38 defectos, todos aplicados;
  el más serio, mío: «`prf_inAxC` se retiró», cuando es teorema desde el 2026‑07‑20. Los dos más serios de los agentes:
  que no quedaba nada pendiente de `ax24` (era una instancia del axioma y hoy no hay derivación) y que `ChainNegPrf`
  consumía `prf_lineWF_of_chainOk` (sólo lo cita en docstrings).
* **La evidencia**, en `doc/registro/2026-10-12-t02-teoria/`: el script y los resultados de los dos workflows, los cinco
  informes del 2026‑10‑14, la salida del sondeo, la medición de leanchecker (§7), y en `comentarios/` los encargos, los
  siete informes y las tres revisiones del lote; el build y los controles del día.

### 7 · Lo que NO dice

* «Contiene a PA» es por LECTURA de las definiciones: ningún teorema del árbol lo enuncia. La conservatividad sobre PA,
  la traducción aritmética, la derivación de `listInd` desde `ind` y una D1 sin `ind` siguen sin hacer, y no se cotizan.
* No se toca `TEOREMAS-E-HIPOTESIS.md` (es T09, ADR‑135), ni `PLAN-LIBRO.md` ni `doc/book/`: el libro está en espera por
  decisión del propietario (2026‑10‑14), y sus líneas sobre Q++, `⊬G` a secas y la consistencia, que el censo encontró,
  quedan para cuando se retome.
* **leanchecker no cabe hoy en local**: medido el 2026‑10‑14, el de RPP pide más de 35 GB de memoria privada y agota la
  del sistema (dos servicios de Windows, CDPUserSvc y CloudBackupRestoreSvc, retienen unos 16 GB); el de FOL y
  TheoryFramework pasa (25 s). El 2026‑10‑12 pasó entero (526 s). Lo pasa la CI antes de que este commit llegue a
  `master` (ADR‑136).
* Las marcas `Last updated` de `README.md`, `AXIOMS.md`, `GODEL-STATUS.md` y los demás documentos con deuda no se suben:
  sus cuerpos siguen con secciones viejas, y la marca diría que están al día. Siguen en `E_DEUDA`; la de `AXIOMS.md` y el
  «Resumen al día» de `GODEL-STATUS.md` llevan una nota fechada.
* No se retiran `d3_prf_of_sigma1` ni `d3_prf_of_reflect_bounded` (T05: quedan marcados VACUOS), ni se corrigen las
  citas `fichero:línea` desplazadas de los documentos de registro (T34).
* FOL tiene dos frases desactualizadas (`../FOL/FOL/Derives0.lean:107-108` y la copia de M‑11 de `:181-182`, ADR‑133), y
  esperan a un commit de FOL.

🔑 *Una lista de axiomas no es una teoría: lo que la hace contener a PA es un constructor de `Prf`, `ind`, y ningún
documento lo decía.*

**Véase también:** ADR‑054 §4 (la conservatividad, descartada), ADR‑115 (la capa `⊢`), ADR‑117 (el ancla), ADR‑120 (el
modelo y `prf_sound`), ADR‑132 (la auditoría), ADR‑135 (T09).

## ADR-135: 📋 TEOREMAS-E-HIPOTESIS, al día —`⊬¬G` existe— y la pregunta «¿qué usa la prueba?», MEDIDA en tres clases; el control [T]

**Fecha:** 2026-10-14 · **Estado:** ✅ (este commit) · **Ámbito:** `TEOREMAS-E-HIPOTESIS.md` (reescrito: banner, §0, §1
con la columna nueva y la fila de Rosser, §2, §3, §4 y §5); `check-doc-sync.bash` (el documento entra en AUTHORITATIVE, y
el control `[T]`); `sondeos/InduccionTitulares.lean` (`#modelo`); notas en `PLAN-PRUEBAS.md` (V8, P‑2), `NEXT-STEPS.md`,
`sondeos/README.md` y la auditoría; y `doc/registro/2026-10-14-t09-teoremas/`. Es T09 (P1) de
`doc/AUDITORIA-SUELO-2026-10-12.md`.

### 1 · Lo que decía el documento

Se contradecía en tres sitios (MEDIDO por la auditoría): §2 decía «`⊬¬G` NO EXISTE sobre `Prf`» con la fila de
`goedel_I_neg` en §1; una línea decía que D1 y D3 llevaban `[AnclaEq]` —retirada en ADR‑118— y, tras las seis filas que
insertó ADR‑121, colgaba de `tarski_semantico`; y §5 decía «lo único supuesto es `ConsistentH`» mientras §4 lo daba por
TEOREMA. No estaba en AUTHORITATIVE, `[E]` lo daba por saldado, y `PLAN-PRUEBAS.md` (V8) lo llamaba «la única defensa
contra F‑1», llevada a mano. Todos los errores rebajaban lo demostrado; ninguno lo sobrevendía.

### 2 · La pregunta nueva: ¿qué usa la prueba?

Desde ADR‑120, `ConsistentH` es un teorema, y para toda `P`, `(ConsistentH → P) ↔ P`: una hipótesis `hcon :
ConsistentH` se descarga sola, y el enunciado ya no distingue «basta la consistencia» de «usa la verdad en ℕ». Lo
distingue lo que NOMBRA el cierre de dependencias de la prueba. Tres clases, con el criterio que propone T08: una
constante es «de la semántica» si vive en `FOL.Metamath.Semantics` o en `ROBINSON_PlusPlus.Meta.SolidezPrf`.
* **(i)** el cierre no nombra nada de la semántica;
* **(ii)** la nombra, pero sólo a través de `consistencia`: cortado ese nodo, no queda ninguna;
* **(iii)** la nombra también por otro camino: la verdad en `MNV V₀` más allá de la consistencia.

MEDIDO el 2026‑10‑14 con `#modelo` (`sondeos/InduccionTitulares.lean`; el sondeo entero, 19 s):
* (i): D1 (`repr_pos'_prf`), D2 (`d2_prf`), D3 (`d3_prf_real`), `prf_godelCN_fixedpoint`, `prf_con_imp_godel`,
  `goedel_first_prf`, `goedel_second_prf` y `prf_tarski`;
* (ii): `goedel_I`, `goedel_II` y `tarski`;
* (iii): `goedel_I_neg`, `godelCN_indecidible`, `godelCN_verdadera`, `con_verdadera`, `modelo_prov_iff` y
  `tarski_semantico`.

A `consistencia` la clase no se le aplica: es el nodo por el que se corta, y con ella de raíz no se corta nada (la
primera versión del sondeo la daba como (iii) por construcción; lo vio la revisión).

Lo que dice: `⊬G` desde la consistencia simple (`goedel_first_prf`, clase i) es un teorema con contenido —su prueba no
mira el modelo—, y `goedel_I` sólo lo usa para descargar la hipótesis. La mitad `⊬¬G` (`goedel_I_neg`) es de la clase
iii: usa la verdad de `T_Prf` en ℕ, que es más que su consistencia; desde la consistencia simple sería Rosser (T01).

### 3 · El control `[T]`

La regla del documento («una fila AUSENTE es un fallo») se cumplía a mano. `[T]` la comprueba con un universo
DECLARADO, `T_UNIVERSO`, de los 18 titulares de §1 y §3: que cada uno esté declarado en el build de RPP, que tenga UNA
fila —el nombre en negrita, **`x`**, en la columna del nombre: la primera en §1, la segunda en §3; no cuenta en otra
columna ni tachado— y que ninguna fila sobre. El universo no sale de `check-footprints.bash`, porque su tabla tiene
filas que no son titulares (`consistentH_de`, `V₀_eq_codigo`, `v_ancla`). El autotest compara la salida EXACTA sobre un
documento sintético (un nombre en la hipótesis, uno tachado, uno tras el fin de §1, una fila de §3, una intrusa, una
repetida) con los cinco fallos esperados. Probado (`doc/registro/2026-10-14-t09-teoremas/control-T-2026-10-14.txt`):
verde sobre el documento; rojo sin la fila de `tarski_semantico` y con una intrusa; rojo con el nombre sólo en la
hipótesis de otra fila; y los cinco mutantes del bloque (sin extractor, sin cierre de sección, columna equivocada, sin
quitar tachados, sin contar repeticiones) dan «NO PUDE MEDIR».

**La revisión adversarial** (un agente de sólo lectura, unas 120 afirmaciones) encontró 17 defectos, todos aplicados.
Los tres de más peso: «una mitad `⊬¬G` desde la consistencia simple es el teorema de Rosser» era falso —para `G`,
`⊬¬G` no sale de la consistencia, porque T+¬Con es consistente y demuestra `¬G`; Rosser cambia de sentencia—; la
clase (iii) de `consistencia` era un artefacto del corte; y la primera versión de `[T]` daba verde con el nombre en la
columna de la hipótesis, y su autotest, que contaba fallos, no distinguía un extractor roto.

### 4 · Lo que NO dice

* `[T]` no comprueba que la columna «¿qué usa la prueba?» sea la medida: eso lo mide `#modelo`, fuera de la CI, y lo
  mecanizará T08 en el build. Tampoco decide qué es un titular: uno nuevo se añade a `T_UNIVERSO` en el mismo commit.
* El criterio de `#modelo` es por ESPACIO DE NOMBRES: una prueba que usara la verdad en ℕ sin pasar por esos dos no la
  vería. La aritmética de la metateoría sobre ℕ (`ModeloCodigo`) no cuenta como semántica.
* D1, D2 y `prf_con_imp_godel` siguen sin fila de footprint (T11b).

**Véase también:** ADR‑024 (qué era `ConsistentOmega`), ADR‑117 (el ancla), ADR‑120 (`consistencia`), ADR‑121
(`goedel_I_neg`), ADR‑134 (la teoría y el sondeo de la inducción); T01 (Rosser) y T08 (la pureza del cierre).

## ADR-136: 🔒 `master` protegido —sólo entra un commit con la CI ya verde— y las decisiones del propietario del 2026‑10‑14

**Fecha:** 2026-10-14 · **Estado:** ✅ (este commit; la protección se activa en GitHub justo después de que su CI salga
verde) · **Ámbito:** `.github/workflows/build.yml`, `AI-GUIDE.md` (`guarda_y_sube`), `guarda_y_bloquea.bash` (un aviso),
la protección de la rama `master` en GitHub, `doc/AUDITORIA-SUELO-2026-10-12.md` (las decisiones y el estado de T14) y
`doc/registro/2026-10-14-t01-rosser/informe.md`. Es la parte de RPP de T14.

### 1 · Por qué

La CI corría DESPUÉS de que el commit llegara a `master`: un rojo se veía cuando ya estaba publicado. Pasó con ADR‑120,
rojo en `[E]` y arreglado en el commit siguiente. El propietario decidió el 2026‑10‑14: «se protege el repositorio
exigiendo la CI en verde», con el flujo de rama `ci/` y avance rápido de `master`, y sin excepción para el administrador.

### 2 · Lo que se hizo

* **`build.yml`.** El `push` dispara también en las ramas `ci/**`. El job del libro no corre en ellas: en una rama nueva
  `github.event.before` es cero, y su regla «ante la duda, ejecutar» compilaría el PDF en cada push. El libro está en
  espera (T49), y sus controles siguen corriendo en el push a `master`.
* **La protección** (API de GitHub, `PUT repos/julian1c2a/ROBINSON_PlusPlus/branches/master/protection`): la
  comprobación obligatoria es `lake build`, el job entero (build de RPP y de FOL, leanchecker, sorry, estratos,
  footprints, doc‑sync y warnings). Lleva `strict` y `enforce_admins: true`; no exige revisiones ni restringe quién
  empuja. El job del libro no es obligatorio.
* **`guarda_y_sube`** (AI‑GUIDE): el paso 5 en tres tiempos. Primero `git push origin HEAD:refs/heads/ci/<nombre>`;
  después, esperar el verde; y por último `git push origin HEAD:master` y borrar la rama.
* **El primer uso** es este mismo push: los commits de ADR‑134, ADR‑135 y éste, juntos en `ci/2026-10-14`.

### 3 · Las decisiones del propietario del 2026‑10‑14

* **T26 y T28:** `CURRENT-STATUS-PROJECT.md` y `GODEL-STATUS.md` se REESCRIBEN; no se retiran.
* **T49, el libro:** sigue vivo, en espera hasta que el proyecto esté más adelantado. No se toca `doc/book/` ni
  `PLAN-LIBRO.md`.
* **T14, gobierno de RPP:**
  - `master` se protege exigiendo la CI verde (§2).
  - Un módulo de RPP se congela sólo cuando sea SEGURO que su fase está cerrada. Hoy no se congela ninguno. Los
    candidatos que nombraba T14 (`Consistencia`, `SolidezPrf`, `TarskiPrf`) pueden tocarse todavía: T75 (el control
    del ancla y la generalización a todo `Estandar M`), T61 (el `Classical.choice` de `prf_sound`), T62 (`Prf` con la
    teoría como parámetro) y Rosser.
* **T01, Rosser:** sin decidir. El propietario pidió más información para ver bien las diferencias entre las opciones.
  El informe, de un agente de sólo lectura, está en `doc/registro/2026-10-14-t01-rosser/informe.md`: el enunciado y lo
  que prueba cada opción, lo que se construye, el coste (ESTIMACIONES con su fuente) y el riesgo.

### 4 · Lo que NO cubre

* FOL no se protege: es otro repositorio, con su propio chat. La parte de FOL de T14 (activar el gancho, el CR, los
  renombres y un paso de CI sobre los congelados) sigue abierta.
* Si GitHub Actions cae, `master` queda bloqueado. El administrador puede levantar la protección, y eso queda en el
  registro de GitHub.
* El primer push a `master` repite la CI: el push a `master` también la dispara, y no hace daño.

**Véase también:** ADR‑073 (el par certificado), ADR‑116 (los controles de la CI), ADR‑120 (la CI roja que llegó a
`master`), ADR‑134 y ADR‑135.

## ADR-137: 🧭 Rosser se hará con la TEORÍA COMO PARÁMETRO del verificador (opción a‑ii de T01) y T08 como criterio de aceptación; y dos frases de FOL al día

**Fecha:** 2026-10-14 · **Estado:** ✅ decidido (este commit); el trabajo, por hacer. ✏️ *(2026‑10‑16, [ADR‑145](#adr-145))*: el
enunciado sigue; el DISEÑO de §1 (un verificador con la teoría como parámetro, `PrfL`) lo sustituye la REDUCCIÓN de
ADR‑144: T+E es `PrfH E`, y su predicado de prueba, el de T delante de `impChain` · **Ámbito:** la decisión de T01, que
arrastra la de T62; `doc/AUDITORIA-SUELO-2026-10-12.md` (T01, T08, T62 y las decisiones), `NEXT-STEPS.md`; y FOL
`f9941dc` (`FOL/Derives0.lean`, sólo comentarios).

### 1 · La decisión

El propietario eligió el 2026‑10‑14, tras leer `doc/registro/2026-10-14-t01-rosser/informe.md`, la opción **(a‑ii)**,
con **T08** como criterio de aceptación. Las opciones descartadas son (a‑i), la familia autoanclada; (b), NegNum por la
ruta P con T08 sobre `T` fija; y (c), no hacer Rosser sobre `T`.

* **El enunciado** (aproximado; nada de esto existe): un verificador con la teoría como parámetro, `lineWF g x` y
  `chainOk g c p`, donde la regla `thy` mira `In (carc x) g` en vez de `axiomsCodeT`. Su `Prf` es `PrfL Γ`, y la sentencia
  de Rosser es la de cada teoría:
  `rosser_ext (E) (hE : ∀ φ ∈ E, IsSentence φ) (hcon : ¬ PrfL (axioms ++ E) ⊥) : ¬ PrfL (axioms ++ E) (R (axioms ++ E)) ∧
  ¬ PrfL (axioms ++ E) (neg (R (axioms ++ E)))`. Es decir: si T+E es consistente (E finita), la sentencia de Rosser de
  T+E es indecidible en T+E. `Prf` es la instancia E = [].
* **Por qué tiene contenido.** La hipótesis `hcon` puede fallar: con E = [⊥] falla. Y hay miembros consistentes que no
  son sólidos, como T+¬Con_T, en los que la solidez no puede sustituir a la consistencia. Es la opción más cercana al
  Rosser de los libros: expresa T+¬Con_T y T+G_T, y con ellas la cadena de incurabilidad.
* **T08 encima.** Un control de pureza del cierre, en el build, comprobaría que la prueba de la instancia no pasa por la
  semántica (`FOL.Metamath.Semantics`, `Meta.SolidezPrf`). Así el argumento es el sintáctico de Rosser y no una vuelta
  por el modelo, que con E = [] haría decorativa la hipótesis. Es el mismo criterio que mide hoy `#modelo` (ADR‑135).
* **Lo que no da** (ninguna opción lo daba): extensiones r.e. infinitas, ni teorías por debajo de los esquemas de `Prf`.

### 2 · Lo que cuesta y lo que arriesga (del informe; las cifras de radio, MEDIDAS con grep; el resto, ESTIMACIÓN)

* De los 107 axiomas de codificación, 25 nombran `lineWF` o `chainOk`, y dos nombran `axiomsCodeT`: `ax_lineWF_thy` y
  `ax_vpf_thy`. La maquinaria de D1 que habría que generalizar o duplicar son 634 líneas de `prf_lineWF_*` y 197 de
  `prf_chainOk_track`. El refactor se cotizó en «semanas», sin medir. Es la opción de más radio.
* **Riesgos:**
  - reabre el verificador y el modelo (`ModeloCodificacion`: revalidar los 107 y su interpretación);
  - puede cambiar `axioms`, V₀, el ancla y el numeral de G;
  - «una segunda constante con su ancla no basta»: hace falta un verificador entero (CRI‑02, corrección e);
  - la lección de F1 sigue: un ancla que se contiene a sí misma no se puede postular (ADR‑117).

### 3 · El orden

1. **T08**, ya: una tarde (ESTIMACIÓN); sirve desde hoy para los titulares de la clase (i) de ADR‑135 y será el criterio
   de aceptación de Rosser. Su maquinaria está en `sondeos/ChoiceFrontera.lean` y en `#modelo`.
2. **La medición de alcance** que pide T62: cuántas declaraciones nombran `axioms`, `axiomsCodeT`, `lineWF` o `chainOk`
   con un argumento de teoría, y qué cambia en el ancla al añadir una lista.
3. **El ADR de diseño** (T62, opción ii, ya elegida): la firma de `lineWF`/`chainOk` con la teoría, cómo se ancla el
   código de cada T+E sin volver a F1, qué pasa con V₀ y con los 107, y el plan de transporte de lo ya probado.
4. **El sondeo de viabilidad**, con sus controles: `PrfL (axioms ++ [neg consistencyFormula']) ⊥` NO derivable (INFERIDO:
   la consistencia de T+¬Con sale de `goedel_II` y la deducción); `PrfL (axioms ++ [⊥]) ⊥` derivable; y la hipótesis de
   `rosser_ext` refutable para esa E. Después, el refactor y NegNum/PosNum sobre el verificador nuevo. La Etapa 0
   (`RosserReflexion`, `RosserBasura`) se porta.

### 4 · FOL: dos frases al día (`f9941dc`, empujado antes que este commit, M‑12)

* La cabecera de `FOL/Derives0.lean` decía que el módulo sólo entra por el barrel `FOL`, que RPP no importa. Desde
  ADR‑121 (Tarski) le llega por `Meta/TarskiPrf.lean` → `FOL.Lift0` → `FOL.Eigenvariable` → `FOL.Derives0`; RPP sigue
  sin usar `Derives`.
* El docstring del encaje copiaba M‑11 al revés («sobre `Derives` esa inducción sería ilegítima»). La inducción es
  válida siempre; lo que puede ser falso es el axioma que contradiga lo inducible (ADR‑133). Era la copia de FOL que
  ADR‑133 dejó pendiente.
* Sólo comentarios: el build de FOL (58 jobs), `check-doc-sync`, `check-sorry` y `check-axioms` de FOL salieron verdes.

**Véase también:** ADR‑117 (F1 y el ancla), ADR‑122 §2 (Rosser re‑medido), ADR‑123…126 (la Etapa 0), ADR‑135 (las
clases y `#modelo`), ADR‑136 (las decisiones del día); T01, T08, T62, T64 y T66 de la auditoría.

## ADR-138: 🧭 La consistencia que da `consistencia` es RELATIVA a Lean —PRA ⊢ Con(Lean) → Con(T_Prf)— y no puede ser absoluta; dicho en los banners, en TEOREMAS §4 y en PLAN-LIBRO

**Fecha:** 2026-10-16 · **Estado:** ✅ (este commit) · **Ámbito:** sólo documentación: los banners de `README.md`,
`AXIOMS.md`, `REFERENCE.md` y `DECISIONS.md`, y la línea «Hay prueba de consistencia» de `README.md`;
`TEOREMAS-E-HIPOTESIS.md` (banner, la fila de Rosser, §4 y §5); `AXIOMS.md` §0.2; `PLAN-LIBRO.md`, capítulo 6 (una
excepción puntual a T49, pedida por el propietario); `NEXT-STEPS.md` y `doc/AUDITORIA-SUELO-2026-10-12.md` (la nota).

### 1 · Por qué

La pregunta del propietario (2026‑10‑16): «la consistencia para un modelo de aritmética Q será necesariamente un modelo
de consistencia relativa […] ¿Podemos estar confundiendo consistencia con consistencia relativa?». La respuesta,
leída en el árbol:

* **En el código, no.** `consistencia : ConsistentH` es un teorema de Lean y dice lo que dice. Un teorema de Lean es,
  por construcción, relativo a Lean.
* **En la prosa, sí, en dos sitios.**
  - Los banners «`ConsistentH` es un TEOREMA del build: Gödel I y II SIN HIPÓTESIS» (README, AXIOMS, REFERENCE y
    DECISIONS) y la línea «Hay prueba de consistencia» de README se leen como consistencia absoluta.
  - `PLAN-LIBRO.md`, capítulo 6, decía «la metateoría no tiene que ser más fuerte que la teoría de la que habla». Se
    escribió el 2026‑09‑09, cuando los titulares eran condicionales. Para los que hoy van sin hipótesis es FALSO.
* **Nadie lo decía.** Buscado el 2026‑10‑16 en todos los `.md` (grep de «relativ», «Con(Lean», «consistencia de
  Lean»): ninguna mención de que la consistencia sea relativa a Lean. Lo más cercano, `TEOREMAS-E-HIPOTESIS.md` §5,
  «lo único que se supone es el núcleo de Lean y sus tres axiomas»: correcto, pero sin decir que con el núcleo se
  supone su consistencia.

### 2 · Lo que se fija (el detalle, en `TEOREMAS-E-HIPOTESIS.md` §4)

* **Qué garantiza `consistencia`, fuera de Lean:** PRA ⊢ Con(Lean) → Con(T_Prf). Con(T_Prf) es Π₁: si `T_Prf` fuera
  inconsistente, la derivación de `⊥` sería un objeto finito, Lean construiría con ella un término de `Prf ⊥` y, con
  `consistencia`, derivaría `False`. Y eso, si el núcleo implementa bien su teoría de tipos: un error del núcleo no lo
  excluye ningún control.
* **Absoluta no puede ser.** `T_Prf` contiene a PA (ADR‑134). Por Gödel II, ninguna teoría contenida en `T_Prf`
  demuestra Con(T_Prf), salvo que `T_Prf` sea inconsistente: la metateoría que descarga `ConsistentH` es por fuerza
  más fuerte. La de Lean lo es con mucho (equiconsistente con ZFC más infinitos inaccesibles: Carneiro, 2019; de la
  literatura, no medido).
* **A qué titulares alcanza.** A `consistencia` y a las clases (ii) y (iii) de ADR‑135. `goedel_I`, `goedel_II`,
  `goedel_I_neg` y `tarski` implican `ConsistentH` (de `Prf ⊥` sale cualquier fórmula). Los demás de la clase (iii)
  hablan de la verdad en `MNV V₀`, que la teoría no puede definir. La clase (i), con los condicionales
  `goedel_first_prf` y `goedel_second_prf`, no pasa por el modelo. Que para ella baste una metateoría débil es lo
  esperable, y **no está medido**.
* **Dos sentidos de «relativa».** Probada en S (S ⊢ Con(T), que da PRA ⊢ Con(S) → Con(T): el de `consistencia`, con
  S = Lean), y equiconsistencia entre teorías objeto (PRA ⊢ Con(HA) ↔ Con(PA), Gödel–Gentzen). Gentzen (PRA + TI(ε₀) ⊢
  Con(PA)) es del primer tipo con una S mucho más débil que Lean. Para `T_Prf` pediría además reducirla a PA, y eso no
  está hecho.

### 3 · Lo que se cambió

* **Banners** de README, AXIOMS, REFERENCE y DECISIONS: el titular dice «sin hipótesis DENTRO de Lean» y «la
  consistencia es RELATIVA a Lean», con un párrafo debajo. La línea de README dice «RELATIVA a Lean», con su nota.
* **`TEOREMAS-E-HIPOTESIS.md`**: §4, la sección nueva; §5, la consistencia del núcleo entre lo que se supone; el
  banner, una línea. De paso, el banner y la fila de Rosser decían «por decidir (T01)», caducado desde ADR‑137: al día.
  Su marca sube a hoy, y una marca responde del cuerpo entero ([E]).
* **`AXIOMS.md` §0.2**, punto 1: con el núcleo se supone su consistencia.
* **`PLAN-LIBRO.md`**, capítulo 6: la frase, acotada a los condicionales, y la nota de por qué.
* **Las marcas.** README, AXIOMS, REFERENCE y PLAN-LIBRO están en la deuda de `[E]` (`E_DEUDA`), y su
  `**Last updated:**` NO sube. El cambio toca un banner y un párrafo, no el cuerpo. Subirla certificaría un cuerpo que
  no se ha revisado, que es justo el defecto que `[E]` existe para cazar.

### 4 · Lo que NO cubre

* La misma frase, sin acotar, sigue en `doc/book/MATERIALES.md` §1.4 y en la lección del principio de
  `doc/book/capitulos/cap-objeto-y-meta.tex`. No se tocan mientras el libro esté en espera (T49, ADR‑136 §3).
* Los demás documentos que dicen «SIN HIPÓTESIS»: `CURRENT-STATUS-PROJECT.md` y `GODEL-STATUS.md` (los reescriben T26
  y T28), los bloques viejos de NEXT-STEPS y los `doc/REFERENCE-*`. T33, la fuente única del estado, lo resolvería de
  una vez (ADR‑139, paso 2).
* La fuerza de la metateoría que pide la clase (i): medirla pediría traducir las pruebas a una aritmética débil.

**Véase también:** ADR‑120 (`consistencia`), ADR‑134 (`T_Prf` contiene a PA), ADR‑135 (las tres clases), ADR‑136 §3
(T49) y ADR‑139.

## ADR-139: 🟡 PROPUESTO — acotar el proyecto en tres pasos (archivar los sondeos, congelar la historia, contratos de capa), con el cono de los titulares MEDIDO por declaración

**Fecha:** 2026-10-16 · **Estado:** 🟡 PROPUESTO; decide el propietario (§4). Lo único hecho es la medición (§2).
✏️ *(el mismo día, [ADR‑140](#adr-140))*: ✅ aprobados los pasos 1 y 2, con las opciones recomendadas; el paso 3,
decidido en su forma (capas DENTRO de RPP), se ejecuta después ·
**Ámbito:** `sondeos/ConoTitulares.lean` (nuevo), `doc/registro/2026-10-16-cono/` (su salida), `sondeos/README.md` y
`doc/registro/README.md`. El plan, si se aprueba, toca `sondeos/`, `DECISIONS.md`, `NEXT-STEPS.md`, `CHANGELOG.md`,
los banners y los `import` de las capas.

### 1 · Por qué

La pregunta del propietario (2026‑10‑16): el proyecto es grande, se desarrolla con Claude y una ventana de contexto de
1 M de tokens. ¿Habrá pérdida de información? ¿Qué se puede hacer para acotarlo, y con él el contexto que hace falta?

Medido ese día (`git ls-files`, `master` = `377c44b`, antes de este ADR):

| | ficheros | líneas | bytes |
|---|---|---|---|
| Lean del build (`ROBINSON_PlusPlus/`) | 113 | 52 442 | 2,9 MB |
| Lean de `sondeos/` (92 en la raíz y 2 en `lintlab/`) | 94 | 77 287 | 4,2 MB |
| Markdown | 72 | 46 004 | 3,55 MB |
| Lean de FOL | 163 | 30 937 | 1,45 MB |

ESTIMACIÓN, no medida (de 3 a 4 bytes por token para este texto): la prosa sola ocupa de 0,9 a 1,2 M tokens, y el Lean
de RPP de 1,8 a 2,4 M. El repositorio no cabe en una ventana, ni tiene que caber: Claude lee bajo demanda. La pérdida
se da en tres sitios: el resumen automático dentro de una sesión, que pierde detalle (lo primero, si una cifra se midió
o se infirió); entre sesiones, donde sólo queda el repositorio y la memoria; y la prosa caducada que se lee como vigente.
Lo que el build vuelve a comprobar no se pierde. Por eso el plan saca del camino lo que no comprueba nadie.

### 2 · La medición: el cono de los titulares, por declaración

`sondeos/ConoTitulares.lean` (80 s, `lake env lean`). Es el cierre de dependencias de los 18 titulares de `T_UNIVERSO`
por tipos, valores y proyecciones, asignado a las declaraciones del fuente. **Ámbito:** es el cono del NÚCLEO, lo que
el kernel necesita para comprobar los titulares; fuera del cono no quiere decir «se puede borrar», porque una táctica,
una notación o un lema de `simp` que no quedó en el término hacen falta para elaborar. Los controles del sondeo
pasan (la clase (i) no nombra `SolidezPrf` y `consistencia` sí, como mide `#modelo`; nada de `VerifierSound` dentro;
cada titular dentro; y sin dueño quedan 3 auxiliares de Lean). Salida entera: `doc/registro/2026-10-16-cono/`.

| capa | ficheros importados | con algo en el cono | líneas | fuera de toda declaración | declaraciones | en el cono | líneas en el cono |
|---|---|---|---|---|---|---|---|
| RPP (los 112 módulos y los dos barriles) | 114 | 101 | 52 634 | 18 012 | 3 623 | 2 847 (79 %) | 28 578 |
| FOL (de sus 163) | 12 | 4 | 2 840 | 1 008 | 193 | 48 (25 %) | 481 |

* **El build ya es estrecho.** Fuera del cono quedan 776 declaraciones con 6 044 líneas; la lista, declaración a
  declaración, en `fuera-del-cono.txt`. Hay además 18 012 líneas fuera de toda declaración: comentarios, docstrings
  de módulo, `example`, `#print` y líneas en blanco.
* **D3 es el 92 % del cono.** `d3_prf_real` arrastra 2 444 declaraciones y 26 880 líneas. `goedel_first_prf`, 720 y
  5 164. La clase (i) entera, 2 478 y 27 158. Lo que sólo piden `consistencia` y las clases (ii) y (iii), 417 y 1 901.
* **21 ficheros importados no aportan nada al cono.**
  - El subárbol de T66, CONFIRMADO: `ChainNegPrf`, `VerifierSound`, `OmegaReflect`, `ChainDecode` y `CodeDecode`.
  - `Sigma1BoundedPrf` (T05) y `Full/PrimeFactor`.
  - Tres que la medición por módulo no veía: `CodeDistinct`, `ReflectionPrf` y `Sigma1TrackedPrf`. Se importan, y el
    núcleo no usa nada suyo.
  - `Minimal/SymLit`, la macro `sym!`: es elaboración pura y hace falta.
  - Los dos barriles.
  - Ocho de FOL: `Deduction`, `Derives0`, `Eigenvariable`, `Lift0`, `Tactics`, `Theorems.Derived`, `Theorems.Impl` y
    `Theorems.Neg`. Es la capa `Derives` y sus vecinos, la de T74.

⇒ El volumen que sobra NO está en el build. Está en `sondeos/` (77 669 líneas con `ConoTitulares`) y en la prosa:
`DECISIONS.md` tiene 10 480 líneas, y ADR‑001…ADR‑130 ocupan las líneas 1–9 952; `NEXT-STEPS.md` tiene 4 600, y su
sección «PUNTO DE REANUDACIÓN» va de la línea 7 a la 4 118, y lo que sigue son las secciones de junio y julio.

### 3 · El plan (PROPUESTO)

**Paso 1 · Archivar los sondeos** (T06 y luego T10).
1. Primero T06: el runner con `lake lean`, con un TSV de hoy. La cifra «35 de 88 compilan» es de ADR‑127
   (2026‑10‑05) y no se ha vuelto a medir.
2. Cada sondeo, en una de cuatro clases, como pide T10: CONTROL (a la CI con T06, bloqueante), REGISTRO (compila y se
   cita como evidencia), REPARAR o ARCHIVAR.
3. Antes de quitar nada, la etiqueta `archivo/sondeos-2026-10`. `sondeos/README.md` conserva una tabla de archivados
   en otro formato de fila, para que `[H]` no pida el fichero, con el nombre, la etiqueta y lo que midió; el resultado
   vive en su ADR.
* **Efecto:** sin medir hasta T06. La cota superior son las 77 669 líneas menos lo que se quede.
* **Riesgo:** perder un control negativo (`AnclaEqInconsistente`, `MetaReglasRefutables`…). Por eso T06 los hace
  bloqueantes en la CI ANTES de archivar nada.

**Paso 2 · Congelar la historia** (T33, T36, T54 y T55).
1. `DECISIONS.md`: ADR‑001…ADR‑130 (líneas 1–9 952) pasan tal cual a `doc/historia/DECISIONS-001-130.md`, y
   `DECISIONS.md` guarda una línea por ADR (número, título, estado, enlace) y los ADR vivos. Coste de los enlaces,
   medido: ningún enlace del árbol a `DECISIONS.md` lleva ancla (`DECISIONS.md#adr-`: 0), así que siguen valiendo (llegan al índice); hay 5 anclas
   internas que arreglar.
   ⚠️ Los controles: el fichero histórico sale de AUTHORITATIVE por diseño, como CHANGELOG. La deuda de `[B]` y de
   `[A2]` que viva en esos ADR quedaría «pagada por exclusión», y eso es un control que deja de comprobar. El traslado
   tiene que ser PURO, sin editar una línea, comprobado por comparación de bytes, y el ADR que lo ejecute lista qué
   deuda sale del universo y por qué.
2. `NEXT-STEPS.md`: se queda el bloque vigente; los anteriores y las secciones viejas de debajo (de la línea 26 al final, unas 4 575) van a
   `doc/historia/`.
3. Los banners (T33): una sola fuente del estado y un puntero de dos líneas en los demás documentos; los banners
   históricos apilados se van con la historia. La fuente propuesta es el banner de `TEOREMAS-E-HIPOTESIS.md`, que ya
   es AUTHORITATIVE y tiene `[T]`.
4. `CHANGELOG.md` (T54): un índice congelado que remite a DECISIONS.
* **Efecto, medido:** salen del camino activo unas 14 500 líneas (9 952 de DECISIONS y unas 4 575 de NEXT-STEPS), más
  los banners (T33: de 21 a 55 líneas en cada uno de siete documentos).

**Paso 3 · Contratos de capa** (T66 y T74, dentro de la política de congelación de ADR‑136).
1. **FOL:** un fichero de contrato GENERADO por el sondeo, no escrito a mano. Lista las 48 declaraciones de FOL que
   el núcleo de RPP usa y lo de elaboración que RPP necesita (tácticas, notaciones). En una sesión se lee el contrato,
   no FOL.
2. **Los imports muertos** (T74): los ocho ficheros de FOL sin nada en el cono salen de los `import` de RPP, si el
   build pasa sin ellos. Es la medida que falta: la elaboración puede necesitarlos.
3. **T66**, como está escrito: después de que Rosser decida qué hereda. ADR‑137 decidió la ruta, no la herencia.
4. **Opcional:** las cifras del cono, como INFORME de la CI (no como control) junto al runner de T06.
* No se congela nada: ADR‑136 lo permite sólo con la fase cerrada.

### 4 · Lo que decide el propietario

1. Paso 1: ¿el orden T06 → T10 → etiqueta y archivo, o se reparan los que no compilan?
2. Paso 2: ¿se corta `DECISIONS.md` en ADR‑130? ¿La fuente única del estado es el banner de `TEOREMAS-E-HIPOTESIS.md`
   o un `ESTADO.md` nuevo?
3. ¿`CHANGELOG.md` queda como índice congelado (T54)?
4. Paso 3: ¿el contrato de FOL, generado, y los imports muertos fuera? Lo segundo depende de T74, que pide además
   decidir si la capa `Derives` de FOL se retira, queda como legado o se reduce a un `abbrev`.

### 5 · Lo que NO cubre

* No se ejecuta nada salvo la medición: ningún fichero se quita.
* La memoria de los chats está fuera del repositorio (T22).
* Las 18 012 líneas de comentarios del build: no se propone quitarlas. Son las notas de procedencia del proyecto, y
  T31 las puso al día.

**Véase también:** ADR‑127 (los sondeos, re‑medidos), ADR‑132 (la auditoría), ADR‑135 (las clases y `#modelo`),
ADR‑136 §3, ADR‑138; T05, T06, T10, T22, T33, T36, T54, T55, T66 y T74 de la auditoría.

## ADR-140: 🧭 Las decisiones del propietario del 2026‑10‑16: capas DENTRO de RPP, la línea de llegada (`T_UNIVERSO` + Rosser + Löb) y ADR‑139 aprobado en sus pasos 1 y 2

**Fecha:** 2026-10-16 · **Estado:** ✅ decidido (este commit) · **Ámbito:** el estado de ADR‑139;
`TEOREMAS-E-HIPOTESIS.md` (§0, la línea de llegada, y la fila de Löb en §1); `doc/AUDITORIA-SUELO-2026-10-12.md` (las
decisiones, T62, T69 y T70); `NEXT-STEPS.md`.

### 1 · Las decisiones

El propietario propuso partir el proyecto en Qpp, «HA», Goedel_I, Goedel_II, Rosser, Gentzen y Tarski, cada uno con su
repositorio. Pidió además que se le explicara qué era «delimitar el alcance». Decidió, tras el análisis de §2:

1. **Arquitectura** (el paso 3 de ADR‑139): capas DENTRO de RPP, con un manifiesto módulo→capa, un control de la
   dirección de los imports y contratos generados. Un repositorio aparte, sólo cuando una capa se cierre. Gentzen nace
   en su propio repositorio.
2. **La línea de llegada de RPP:** los 18 titulares de `T_UNIVERSO`, Rosser y Löb (T70 entra). Gentzen (T69) y el
   libro (T49) quedan fuera de RPP.
3. **Las variantes de la teoría** (Q++ sin inducción, PA, HA sin `p3`): se miden en el ADR de diseño de T62, que
   cotiza también el coste de parametrizar las REGLAS. No se compromete ninguna.
4. **ADR‑139:** aprobados el paso 1 (los sondeos: T06 → T10 → etiqueta → archivo) y el paso 2 (la historia), con las
   opciones recomendadas: DECISIONS se corta en ADR‑130, la fuente única del estado es el banner de
   `TEOREMAS-E-HIPOTESIS.md` y CHANGELOG queda como índice congelado. También la poda de la memoria del chat, que
   está fuera del repositorio.

### 2 · Lo que se midió para decidir

Medido el 2026‑10‑16 con la maquinaria de `sondeos/ConoTitulares.lean`, por la entrada estándar de Lean y sin escribir
nada. Cada capa es lo que AÑADE al cono acumulado de las anteriores:

| capa | qué añade | declaraciones | líneas | ficheros |
|---|---|---|---|---|
| 0 · base | `Prf` y los 142 axiomas | 280 | 984 | 4 |
| 1 · diagonal | el lema diagonal y Tarski sintáctico | 206 | 1 675 | 28 |
| 2 · Gödel I | D1 y `goedel_first_prf` | 245 | 2 574 | 13 |
| 3 · Gödel II | D2, D3 y `goedel_second_prf` | 1 747 | 21 925 | 75 |
| 4 · el modelo | `consistencia` | 334 | 1 409 | 7 |
| 5 · la semántica | los titulares sin hipótesis, W1, E10 | 83 | 492 | 3 |

* El cono de `consistencia` no contiene ninguna declaración de la capa 3. El modelo es una rama que sale de las capas
  0–2, no un piso encima de D3.
* 20 ficheros tienen declaraciones de dos o más capas (10 361 líneas de fichero): es lo que costaría separarlas. 60 son
  de la capa 3 sola.

Las precisiones que se dieron al propietario:
* **Lo construido no es HA.** `Prf` tiene DNE (`p3`) e inducción para toda fórmula: es PA, con los símbolos de
  codificación y la inducción de listas. HA sería sin `p3`. Ningún titular construye un paso DNE salvo `goedel_I_neg`
  (ADR‑134), y por eso es plausible que los condicionales valgan para HA. Es una INFERENCIA.
* **Q++ no se separa hoy.** La inducción no está en la lista de axiomas: son reglas de `Prf`. Y la teoría de los
  titulares incluye los 107 axiomas de codificación y el ancla.
  - Gödel I sobre Q++ es cierto: D1 usa `ind` en cuatro lemas, evitables por lectura (sin comprobar).
  - Tarski sobre Q++ es viable.
  - Gödel II sobre Q++ pide D3 sin inducción con el predicado sin relativizar, que es una cuestión abierta (ADR‑134).
* **Rosser mejora Gödel I, no Gödel II:** de la solidez o la ω‑consistencia a la consistencia simple. Tarski es
  pequeño (la capa 1). Gentzen no comparte nada con D1–D3: necesita notaciones de ordinales y reducción de
  derivaciones.
* **Cada frontera de repositorio tiene un coste, ya pagado con FOL:** M‑12, M‑3, dos chats, PeanoRF bloqueado por un
  cambio de FOL, la CI cruzada (T38) y la subida de la versión de Lean en cada uno (T42).

### 3 · Consecuencias

* ADR‑139: los pasos 1 y 2 se ejecutan ahora (ADR‑141 y ADR‑142). El paso 3 se ejecuta después, en su forma
  decidida, junto con los 21 ficheros importados sin nada en el cono (T05, T66, T74).
* Después, el orden de ADR‑137: T08, el ADR de diseño de T62 (que cotiza también las reglas como parámetro) y el
  sondeo de viabilidad de Rosser.
* Löb tiene una fila ⬜ en `TEOREMAS-E-HIPOTESIS.md` §1, como Rosser, sin nombre entre comillas invertidas: `[T]` sólo
  cuenta titulares declarados.

**Véase también:** ADR‑134 (`T_Prf` y la inducción), ADR‑136 §3, ADR‑137 (Rosser y T62), ADR‑139; T49, T62, T66, T69,
T70 y T74 de la auditoría.

## ADR-141: 🗄️ Los sondeos, medidos con `lake lean` y clasificados: 11 de control en la CI, 28 de registro, 1 a reparar y 53 archivados con la etiqueta `archivo/sondeos-2026-10` (paso 1 de ADR‑139)

**Fecha:** 2026-10-16 · **Estado:** ✅ (este commit) · **Ámbito:** `check-sondeos.bash` (nuevo), `sondeos/CONTROLES.txt`
(nuevo), `.github/workflows/build.yml` (un paso), `check-doc-sync.bash` (`[B]` y `[M]`), `sondeos/pasadas/tabla-2026-10-16.tsv`,
`sondeos/README.md`, los 53
sondeos archivados, `scripts/sondeos_todos.ps1` (retirado), las citas de los archivados en 25 ficheros del build (sólo
comentarios) y en los documentos autoritativos, `AXIOMS.md` §0.2, `doc/registro/README.md`. Es T06 y T10 de la
auditoría, y el paso 1 de ADR‑139, aprobado en ADR‑140.

### 1 · El runner (T06)

`check-sondeos.bash` sustituye a `scripts/sondeos_todos.ps1`.
* Compila con `lake lean`, que pasa los `leanOptions` del lakefile (`autoImplicit` apagado). `lake env lean`, la orden
  de antes, no los pasa.
* Lleva un tiempo límite por sondeo (600 s) y corre dos a la vez. Escribe `sondeos/pasadas/tabla-<fecha>.tsv`.
* Un sondeo que compila con `sorry` sale como SORRY, no como 0.
* Con `--controles` compila sólo la lista de `sondeos/CONTROLES.txt`, y uno que no compile, uno ausente o una lista
  vacía dan ROJO.
* Visto fallar: con un sondeo que no compila y uno ausente añadidos a la lista, rojo (rc 1). Un sondeo de una línea con
  `sorry` sale SORRY; la primera versión buscaba la comilla recta y Lean 4.31 escribe ``declaration uses `sorry` ``, y
  ese fallo lo cazó la propia prueba.

### 2 · La pasada del 2026‑10‑16 (MEDIDA)

**39 de 93 compilan**, 54 no, ninguno por tiempo; 1 539 s en total. Frente a la tabla de ADR‑129 (2026‑10‑05, con
`lake env lean`) cambian dos filas:
* `MDiezEnLaFirma` compilaba con `lake env lean` y no con `lake lean`: «Unknown identifier `axioms`» (l. 108). Con
  `autoImplicit` encendido, el nombre, que ya no estaba en el ámbito, se convertía en una variable. El sondeo probaba
  su enunciado para una lista cualquiera, no para `axioms`. Comprobado: con `--env` compila. Aquí no hace daño (la
  conclusión de ADR‑070 vale para toda lista), pero «compila» medía otra cosa. Es el caso que T06 temía, y lo hay.
* `SubCodesCritica` pasa de TIMEOUT a no compilar: un término ambiguo (l. 132), a los 527 s.

Los otros 86 dan lo mismo, y los cinco nuevos desde entonces compilan.

### 3 · La clasificación (T10)

| clase | n.º | qué es | qué se hace |
|---|---|---|---|
| CONTROL | 11 | vigilan una afirmación de hoy: las refutaciones de lo retirado, los contraejemplos de vacuidad, `AnclaSoundness`, `IteSimboloNucleo` (T77) y la Etapa 0 de Rosser | la CI los compila en cada push (un paso nuevo del job `lake build`, que sigue siendo el check obligatorio) |
| REGISTRO | 28 | compilan y guardan una medida o una prueba citada por un ADR | se quedan; no van a la CI |
| REPARAR | 1 | `A3IsFCBTracked`: no compila, y T10 pide no borrarlo | se queda, marcado |
| ARCHIVAR | 53 | no compilan y no son control | fuera del árbol (§4) |

La lista de cada clase, en `sondeos/README.md` §«Clasificación». No hay ningún duplicado que conservar: los dos que T10
nombraba (`ClausuraSubsttc`, `EvalSubsttc`) no compilan y se archivan con el resto.

### 4 · El archivo

* **La etiqueta** `archivo/sondeos-2026-10` apunta a `41cc70a`, el último commit con los 53 dentro. Se recuperan con
  `git show archivo/sondeos-2026-10:sondeos/X.lean`.
* **Los 53 sumaban 67 913 líneas**, el 87 % de `sondeos/` (77 669 → 9 756, con `lintlab/`). Quedan 40 ficheros en la
  raíz de `sondeos/`.
* **Sus filas del catálogo** pasan TAL CUAL a una tabla «Archivados» al final de `sondeos/README.md`, con la forma
  `` | `X.lean` (archivado) | ``. `[H]` sólo casa `` | **`X.lean`** ``, así que no pide el fichero.
* **Las citas** del build (85, en 25 ficheros; sólo comentarios y docstrings) y de los documentos autoritativos (142)
  llevan la etiqueta delante: `archivo/sondeos-2026-10:sondeos/X.lean`, una ruta que `git show` entiende. 227 en total,
  contadas antes y después. No se tocan las de los documentos de registro (`doc/registro/`, los PLAN, CHANGELOG) ni
  las de `doc/book/` (T49).
* **El censo de `axiom` en los sondeos** baja de cuatro a dos, los de `lintlab/Uso.lean`: `PilotoDiagonal`, que
  suponía los otros dos, está archivado (AXIOMS §0.2).
* **`[B]` y `[M]`** de `check-doc-sync.bash` leen también las declaraciones de los archivados, desde la etiqueta. Así
  una cita que nombra su sondeo sigue exenta. Lo destapó la primera ejecución: el autotest de `[B]` usaba
  `prf_wfAll_objList`, declarado en un archivado, y dio «NO PUDE MEDIR». Hoy el autotest pide dos testigos, `esAC`
  (de `AnclaEqInconsistente`, en el árbol) y `prf_wfAll_objList` (de `ParseWitness`, en la etiqueta). Sin la etiqueta
  da «NO PUDE MEDIR»: visto fallar, borrándola. La CI la tiene porque el checkout es con `fetch-depth: 0`.

### 5 · Lo que NO cubre

* La clasificación de las citas en «procedencia» y «evidencia», con un control (la otra mitad de T10). Las 85 del
  build son notas de procedencia: lo que sostiene el build está en el build.
* Reparar `A3IsFCBTracked`.
* Los ficheros de `lintlab/` no entran en la pasada: no son sondeos de primer nivel y no los vigila `[H]`.

**Véase también:** ADR‑128 (`autoImplicit`), ADR‑129 (la tabla anterior), ADR‑132 (T00, el runner rescatado),
ADR‑139 y ADR‑140; T06, T10 y T77 de la auditoría.

## ADR-142: 🗄️ La historia, a `doc/historia/` por traslado PURO: ADR‑001…130, los bloques viejos de NEXT-STEPS y los banners apilados; la fuente única del estado y CHANGELOG congelado (paso 2 de ADR‑139)

**Fecha:** 2026-10-16 · **Estado:** ✅ (este commit) · **Ámbito:** `doc/historia/` (nuevo: `DECISIONS-001-130.md`,
`NEXT-STEPS-hasta-2026-10-14.md`, `BANNERS.md`); `DECISIONS.md`, `NEXT-STEPS.md`; los banners de README, REFERENCE,
DEPENDENCIES, GODEL-STATUS, AXIOMS, CURRENT-STATUS-PROJECT y DECISIONS; `CHANGELOG.md` (T54), con sus menciones en
README y REFERENCE; `check-doc-sync.bash` (`B_DEUDA` y su tope). Es T33, T36 y T54 de la auditoría, y el paso 2 de
ADR‑139, aprobado en ADR‑140.

### 1 · Lo que se trasladó, y cómo se comprobó

Cada traslado lo hizo un guion que copia el tramo TAL CUAL y lo compara con `diff` contra `HEAD`: tiene que salir
vacío, y salió vacío. Cada fichero de `doc/historia/` lleva una cabecera de tres líneas con su `**Last updated:**`, que
`[E]` exige a todo `.md`, y después el texto sin tocar.

| qué | de | a | líneas |
|---|---|---|---|
| ADR‑001…ADR‑130 | `DECISIONS.md` (10 818 líneas, 708 KB) | `doc/historia/DECISIONS-001-130.md` | `DECISIONS.md` queda en 1 054 (103 KB) antes de este ADR: la cabecera, las MANDATORIES, un índice de una línea por ADR (título y, si lo declara, estado) y ADR‑131 en adelante |
| los bloques hasta el 2026‑10‑05 y las secciones de junio y julio | `NEXT-STEPS.md` (4 613) | `doc/historia/NEXT-STEPS-hasta-2026-10-14.md` | `NEXT-STEPS.md` queda en 58: el bloque vigente y la lista «Pendiente además de Rosser» |
| los banners apilados | README (79), REFERENCE (84), DEPENDENCIES (66), GODEL-STATUS (70), AXIOMS (75), CURRENT-STATUS-PROJECT (274), DECISIONS (72, y su marca vieja «Última actualización: 2026‑09‑10h») | `doc/historia/BANNERS.md` | 720 + 1; en su sitio, un puntero de dos líneas |

Los Markdown activos (fuera de `doc/registro/` y `doc/historia/`) pasan de 42 972 líneas (el 2026‑10‑16, antes de
ADR‑138) a 28 519.

* **La fuente única del estado** (T33) es el banner de `TEOREMAS-E-HIPOTESIS.md`, que ya era AUTHORITATIVE y tiene
  `[T]`. Los siete documentos llevan, donde estaba su banner: «el banner de TEOREMAS‑E‑HIPOTESIS.md es la fuente
  única». Los banners retirados están en `BANNERS.md` con sus anclas `(#adr-…)`, que son las de su documento de
  origen (lo dice su cabecera).
* **La lista de pendientes** (T36) lleva su regla: un punto sale sólo CERRADO con su ADR, o DESCARTADO con una nota
  fechada. Recoge el orden de ADR‑137, Löb, los P0 y P1 abiertos (T04, T04b, T07, T15), el paso 3 de ADR‑139 y lo que
  se había caído de las listas (T17, ADR‑115 §5 y T48), además de T26 y T28.
* **CHANGELOG** (T54): una nota arriba, «congelado en ADR‑113; el registro es DECISIONS.md y `git log`». README y
  REFERENCE ya no lo presentan como el historial vigente.
* **Los enlaces:** ningún enlace del árbol a `DECISIONS.md` lleva ancla, así que los 173 siguen valiendo (llegan al
  índice). De las 5 anclas internas, 2 eran del banner (se van con él), 2 quedan en el fichero histórico apuntando a
  un ADR del mismo fichero (ADR‑115) y 1 sigue en `DECISIONS.md` apuntando a ADR‑140.

### 2 · Las marcas

`DECISIONS.md` y `NEXT-STEPS.md` suben su marca: están fuera de `E_DEUDA` y su cuerpo entero es lo que queda. README,
REFERENCE, DEPENDENCIES, GODEL-STATUS, AXIOMS, CURRENT-STATUS-PROJECT y CHANGELOG están en `E_DEUDA`, y su marca NO
sube. Se les quitó el banner, pero el cuerpo no se ha revisado.

### 3 · La deuda que sale del universo, nombre a nombre

`[B]` mira los documentos autoritativos, y `doc/historia/` no lo es por diseño, como CHANGELOG. 18 entradas de
`B_DEUDA` sólo se citaban en el texto trasladado. No se pagaron leyendo: salen por EXCLUSIÓN. El tope del trinquete
baja de 41 a 23. Los nombres van sin comillas invertidas: con ellas, `[B]` los leería como citas vigentes.
* Viven en `doc/historia/NEXT-STEPS-hasta-2026-10-14.md`: ax_tc_liftfc, pcc_congr_hole_code, pcc_isFCB_tracked,
  pcc_nodeOk_pure, pcc_wfAll_tracked, prf_div2_double_all, prf_isFC_junk (también en el histórico de
  DECISIONS), prf_isFC_nil, prf_isFC_varc, prf_isFCB_bottom, prf_isFormCodeE_str, prf_isTermCodeE_str,
  prf_liftc_arith_open, prf_tc_carc, prf_tc_eqc, prf_tc_nthc y prf_tc_of_cons.
* Vive en `doc/historia/DECISIONS-001-130.md`: prf_tagConcl_code.

Los avisos de `[A2]` (cifras del cuerpo que no cuadran), con `--quick`, bajan de 18 a 2 por la misma razón.

### 4 · Lo que NO cubre

* Los cuerpos de los documentos en `E_DEUDA`. Sin el banner, `[A]` ve ahora el principio de su cuerpo, y dio rojo
  en una línea: «Build 97 jobs» de CURRENT-STATUS-PROJECT, de septiembre, que se marcó con «entonces». Reescribirlos
  son T26, T28 y el resto de `E_DEUDA`.
* T55 (los planes históricos que parecen vivos) y `doc/registro/`, que ya era registro.

**Véase también:** ADR‑072 (`[E]` y su deuda), ADR‑084 (`[B]` y su trinquete), ADR‑139, ADR‑140 y ADR‑141; T33,
T36, T54 y T55 de la auditoría.

## ADR-143: 🔒 T08: el control de pureza del cierre, en el BUILD — los 8 titulares de la clase (i) no nombran la semántica, y si la nombran el build no compila

**Fecha:** 2026-10-16 · **Estado:** ✅ (este commit) · **Ámbito:** `ROBINSON_PlusPlus/Meta/PurezaTitulares.lean`
(nuevo) y el barril `Meta.lean`; `REFERENCE.md` (fila 84y y la cifra de módulos), `TEOREMAS-E-HIPOTESIS.md`
(banner, §1), `doc/REFERENCE-Incompleteness.md` y `CURRENT-STATUS-PROJECT.md` (las cifras), `doc/AUDITORIA-SUELO-2026-10-12.md`
(T08) y `NEXT-STEPS.md`. Es T08 de la auditoría, el primer paso del orden de ADR‑137.

### 1 · Por qué

Desde ADR‑120 `ConsistentH` es un teorema, y una hipótesis `hcon : ConsistentH` se descarga sola. Si un lema de D1–D3
usara la solidez de `Prf`, `hcon` quedaría de adorno con el MISMO footprint, y ningún control lo veía. Lo único que lo
impedía era la forma del grafo de imports: `Consistencia` importa `GodelTwoPrf`. La clase (i) de ADR‑135 lo medía
`#modelo`, en un sondeo, fuera de la CI. ADR‑137 lo fijó como el criterio de aceptación de Rosser: la sentencia de
Rosser de cada T+E tiene que salir del argumento sintáctico, no de una vuelta por el modelo.

### 2 · Lo que hace

`#pureza_titulares`, al final del módulo, corre en cada `lake build`.
* **El recorrido.** Para cada titular de `PUROS` recorre en anchura su cierre de dependencias, sólo por constantes
  del proyecto (RPP, FOL, TheoryFramework). Las aristas son las constantes del tipo y del valor (`allowOpaque`), y de
  un inductivo sus constructores (y al revés).
* **«De la semántica»** se decide por ESPACIO DE NOMBRES y por MÓDULO, no por lista de nombres:
  `FOL.Metamath.Semantics` (el módulo `FOL.Semantics` entero) y `ROBINSON_PlusPlus.Meta.SolidezPrf`. Cuenta también
  una proyección (`Expr.proj`) sobre una estructura de esos dos, que `getUsedConstants` no ve. `ModeloCodigo` no
  cuenta: es aritmética sobre `Nat`, la de la metateoría (T08).
* **El fallo.** Si un titular de `PUROS` nombra la semántica, `throwError` con el camino más corto hasta ella. Si uno
  de `IMPUROS` (`goedel_I` y `tarski`, que llaman a `consistencia`) NO la nombra, también: el criterio estaría ciego.
* **Los 8 de `PUROS`** son la clase (i): `repr_pos'_prf`, `d2_prf`, `d3_prf_real`, `prf_godelCN_fixedpoint`,
  `prf_con_imp_godel`, `goedel_first_prf`, `goedel_second_prf` y `prf_tarski`. La sentencia de Rosser entrará en la
  lista cuando exista.
* **`#pureza a … | x …`** hace el mismo control sobre listas dadas, para los mutantes y para un titular nuevo.
* **Sin `implemented_by` ni `unsafe`.** Usa `getUsedConstants` y `Expr.find?` del núcleo, para no añadir nada al censo
  `@NATIVO` de `check-estratos`.

### 3 · Lo que dio (MEDIDO, 2026‑10‑16)

Los 8 de `PUROS`, PUROS. Sus cierres tienen de 545 constantes del proyecto (`d2_prf`) a 3 269 (`goedel_second_prf`).
Los 2 controles positivos, IMPUROS, por `consistencia ⟶ consistentH_de`. El módulo tarda 55 s en compilar; el build pasa
de 129 a 130 jobs (113 módulos activos) el 2026-10-16.

**Visto fallar**, con un fichero de mutantes que importa el módulo:
* un «condicional» que descarga su hipótesis con `consistencia` → FALLA, con el camino
  `mutante ⟶ consistencia ⟶ consistentH_de`;
* un lema cuya prueba nombra `prf_sound` sin que su enunciado lo diga → FALLA, por `FOL.Metamath.Semantics.Model`;
* `goedel_first_prf` como control positivo → FALLA: «el criterio está CIEGO»;
* lo correcto (`goedel_first_prf` puro, el mutante impuro) → pasa.

### 4 · Lo que NO cubre

* Una prueba que usara la verdad en ℕ sin pasar por esos dos espacios de nombres. Y una estructura de otro módulo que
  sólo se use por proyección y cuya definición nombre la semántica.
* El ENUNCIADO de los titulares y el valor de sus definiciones: es T07, que irá en este mismo módulo.
* Las clases (ii) y (iii) siguen medidas por `#modelo`, en un sondeo de REGISTRO; no hay una lista de ellas en la CI.
* `[T]` no comprueba que `PUROS` sea exactamente la clase (i) de `TEOREMAS-E-HIPOTESIS.md` §1. La regla, escrita allí:
  un titular nuevo de la clase (i) entra en `PUROS` en el mismo commit.

**Véase también:** ADR‑120, ADR‑135 (las tres clases, `#modelo`), ADR‑137 (el criterio de aceptación de Rosser);
T07, T08 y T59 de la auditoría.

## ADR-144: 🧭 El diseño de T62 — una extensión finita T+E por REDUCCIÓN a T: su cálculo es `PrfH E` y su predicado de prueba, el de T delante de `impChain`; ni el verificador, ni los 142, ni el modelo cambian (PROPUESTO)

**Fecha:** 2026-10-16 · **Estado:** 🟡 PROPUESTO; decide el propietario (§6). Cambia CÓMO se construye la opción
(a‑ii) de ADR‑137, no su enunciado. ✏️ *(el mismo día, [ADR‑145](#adr-145))*: ✅ ACEPTADO: R para Rosser; V‑B si
alguna vez hace falta un verificador con parámetro; las variantes de reglas, aplazadas · **Ámbito:** `sondeos/AlcanceT62.lean` y `scripts/alcance_t62.bash` (la medición),
`doc/registro/2026-10-16-t62-alcance/`, `sondeos/ExtensionPorReduccion.lean` (la viabilidad, de CONTROL),
`sondeos/README.md`, `sondeos/CONTROLES.txt`, `doc/registro/README.md`, `doc/AUDITORIA-SUELO-2026-10-12.md` (T62) y
`NEXT-STEPS.md`. Es el paso 2 (la medición de alcance) y el 3 (el ADR de diseño) del orden de ADR‑137; ADR‑143 hizo el 1.

### 1 · Lo que pedía ADR‑137

* **El enunciado de Rosser:** `rosser_ext (E) (hE : ∀ φ ∈ E, IsSentence φ) (hcon : ¬ PrfL (axioms ++ E) ⊥)`.
  Es decir: si T+E es consistente, la sentencia de Rosser de T+E es indecidible en T+E. La hipótesis puede fallar
  (E = [⊥]) y puede valer en miembros no sólidos (T+¬Con).
* **El diseño elegido:** un verificador con la teoría como parámetro, `lineWF g x` y `chainOk g c p`, con la regla
  `thy` mirando `In (carc x) g`, y el cálculo `PrfL Γ`.
* **Lo que debía decir este ADR:** la firma, cómo se ancla el código de cada T+E sin volver a F1, qué pasa con V₀ y con
  los 107, y el plan de transporte de lo ya probado. ADR‑140 añadió el coste de parametrizar también las REGLAS.

### 2 · La medición de alcance (MEDIDA, 2026‑10‑16)

Dos recuentos.
* **El TEXTUAL** (`scripts/alcance_t62.bash`): las declaraciones del build cuyo FUENTE, sin comentarios, nombra el
  grupo. Es el radio de edición.
* **El del TÉRMINO ELABORADO** (`sondeos/AlcanceT62.lean`): las que lo nombran en su tipo o valor. Sale inflado para
  los elementos de la lista de axiomas: la prueba de `a ∈ axioms` hecha con `simp [axioms]` lleva la lista entera, y
  la de `prf_add_zero_t`, de tres líneas, nombra los 22 `ax_vpf_*` (medido).

| grupo | textual: declaraciones · líneas · ficheros | término: declaraciones · en el cono de los 18 · en el de D1 |
|---|---|---|
| G1 la lista (`axioms`, `axiomsBase`, `coreAxioms`, `codingAxioms`) | 324 · 385 · 51 | 349 · 272 · 126 |
| G2 el código y el ancla (`axiomsCodeT`, `axD`, `psiD`, `nD`, `deltaD`) | 40 · 97 · 9 | 311 (inflado) |
| G3 el verificador objeto (`lineWF`, `lineOk`, `chainOk`, `provFormulaC'`, `provCodeC'`) | 372 · 863 · 51 | 400 · 300 · 59 |
| G4 los 25 axiomas que nombran `lineWF` o `chainOk` | 192 · 274 · 15 | 338 (inflado) |
| G4b sólo `ax_lineWF_thy`, el único que nombra `axiomsCodeT` | 11 · 14 · 7 | 277 (inflado) |
| G5 la regla `thy` (`Prfᵢ.thy`, `prf_ax`) | 233 · 255 · 32 | 4 (sólo `Prfᵢ.thy`) |
| G6 las reglas `ind`, `listInd` y `p3` (y las derivadas) | 47 · 65 · 23 | 12 · 11 · 7 |
| G7 el verificador antiguo (`ax_vpf_*`, `validProofFn`) | 50 · 116 · 5 | 298 (inflado) |
| G8 el verificador en el modelo (`lineWFT`, `lineWFN`, `chainOkL`, `chainOkN`) | 34 · 39 · 3 | 59 · 57 · 0 |

**Y el ancla:** los cierres de `godelCN`, de `consistencyFormula'` y de `provFormulaC'` NO contienen la lista de
axiomas, ni su código, ni el ancla. G y Con no dependen de la lista: sólo `ax_lineWF_thy` y el ancla dependen de ella.

### 3 · El hallazgo: T+E no necesita un verificador nuevo (COMPILADO, `sondeos/ExtensionPorReduccion.lean`)

* **El cálculo de T+E ya existe:** es `PrfH E` (`Meta/HilbertDeduction.lean`), `Prf` con las hipótesis E. Con E de
  sentencias es T+E: `gen` sube el contexto, y una sentencia no cambia al subirla (`IsSentence`).
* **Por el teorema de deducción,** `prfH_iff_prf_impChain : PrfH E φ ↔ Prf (impChain E φ)`, con footprint
  `[propext]`. Aquí `impChain E φ` son las fórmulas de E en implicaciones delante de φ, con la cabeza de E más adentro.
* **El código es el de φ con un término delante,** por definición: `formCode_impChain : formCode (impChain E φ) =
  impChainC E (formCode φ)`, sin axiomas. ⇒ El predicado de prueba de T+E se DEFINE con el de T:
  Pf_E(y, x) := Pf_T(y, `impChainC E x`). Un numeral es prueba de φ en T+E sii lo es de `impChain E φ` en T.
* **PosNum_E y NegNum_E** son, literalmente, PosNum_T y NegNum_T sobre `impChain E φ`, llevados a `PrfH E` con
  `prf_to_prfH`. La sentencia de Rosser de T+E es el punto fijo de ρ_E(x) := ∀y (Pf_E(y,x) → ∃z≤y Pf_E(z, ¬x)), por
  `prf_diagonal`, que ya es general.
* **Los controles de CRI‑02, compilados:**
  - `inconsistente_bottom : PrfH [⊥] ⊥`: la hipótesis puede FALLAR;
  - `consistente_neg_con : ¬ PrfH [¬Con'] ⊥`, por `goedel_II` y la deducción: puede VALER en un miembro NO sólido,
    que demuestra ¬Con, falsa en el modelo.
* **T08:** la reducción es sintáctica. `#pureza` en el sondeo da `prfH_iff_prf_impChain` y `formCode_impChain`
  PUROS; `consistente_neg_con`, que pasa por `goedel_II`, sale IMPURO, como control positivo.
* **El enunciado queda así,** con el mismo contenido que el de ADR‑137 (T+¬Con, T+G, hipótesis refutable):
  `rosser_ext (E) (hE : ∀ φ ∈ E, IsSentence φ) (hcon : ¬ PrfH E ⊥) : ¬ PrfH E (R E) ∧ ¬ PrfH E (neg (R E))`.
* **En matemáticas** es la presentación estándar de una extensión finita: Prov_{T+E}(x) ↔ Prov_T(E → x). El argumento
  de Rosser sólo pide que el predicado de prueba represente la demostrabilidad y sea representable numeral a numeral en
  los dos sentidos.

### 4 · Los tres diseños, comparados

| | **R · reducción** (recomendado) | **V‑B · verificador ADITIVO** | **V‑A · verificador parametrizado en su sitio** |
|---|---|---|---|
| qué se construye | Pf_E; PosNum_E y NegNum_E, por transporte; `rosser_ext` | `lineWFg g x` como FÓRMULA (la etiqueta 15 mira `In (carc x) g`; las demás, `lineWF x`); un símbolo nuevo `chainOkG g c p` con dos axiomas (nil, cons); su modelo (`chainOkN` ya es paramétrico en V); D1 para `chainOkG` | `lineWF g x` y `chainOk g c p` en los 25 axiomas, en todo lo que los cita y en el modelo |
| radio sobre lo de T (MEDIDO, textual) | 0 | 0 en G3 y G4; dos axiomas más en la lista, que prueban por `simp [axioms]` las 324 declaraciones de G1 (el radio de compilación, sin medir); 2 validaciones en el modelo | G3 (372 declaraciones, 51 ficheros), G4 (192, 15) y G8 (34, 3) |
| `axioms`, V₀, el ancla, G | nada | +2 axiomas: cambia el VALOR de V₀ y del ancla; G no (no depende de la lista, §2) | cambian los 25 axiomas: V₀ y el ancla cambian de valor, y G también (nombra `chainOk`) |
| el código de T+E | no hace falta: Pf_E usa el de T | g_E := `concat axiomsCodeT ⌜E⌝`, sin ancla nueva: E no contiene su propio código, así que F1 no aparece | ídem |
| coste (ESTIMACIÓN) | 200–400 líneas encima de NegNum y PosNum de T | además, D1 para `chainOkG` (el seguimiento de cadenas, 197 líneas hoy; los lemas por etiqueta para `lineWFg`, derivados de los de `lineWF`) y el modelo; «semanas» (T62) | lo anterior, y además reescribir lo de T |
| qué da además | — | un Prov_{T+E} con su presentación propia (haría falta para Gödel II de las extensiones à la Feferman), y la base de las variantes de reglas (§5) | lo mismo que V‑B |

Ninguno de los tres reduce lo caro de Rosser: NegNum y PosNum de T, que no existen. La ESTIMACIÓN del informe de T01
es de 1 400 a 2 850 líneas.

### 5 · Las variantes de reglas (Q++, PA, HA; ADR‑140)

No son extensiones por axiomas: cambian el cálculo de la propia T, y R no se aplica. Harían falta tres cosas.
* **El cálculo:** `Prf` con las reglas como parámetro, con los constructores `p3`, `ind` y `listInd` condicionados.
  Nombran esas reglas en su fuente 47 declaraciones (65 líneas, 23 ficheros; G6).
* **El verificador:** las etiquetas 14 (`p3`), 18 (`ind`) y 20 (`listInd`) de `lineWF`, condicionadas. Es una cadena
  verificadora con parámetro, al estilo de V‑B.
* **Las pruebas, DENTRO de la variante:**
  - Para Q++, el cierre de D1 construye pasos `ind` en cuatro lemas (`prf_zero_or_succ`, `prf_add_zero_left`,
    `prf_add_succ_left`, `prf_mul_le_mono_right`; medido en ADR‑134). Por lectura, se pueden evitar. Gödel II sobre
    Q++ no: D3 sin inducción es una cuestión abierta.
  - Para HA (sin `p3`), ningún titular construye un paso DNE salvo `goedel_I_neg` (ADR‑134): la clase (i) valdría,
    plausiblemente. Es una INFERENCIA.

**Coste (ESTIMACIÓN):** el de V‑B, más las banderas de regla y los cuatro lemas sin `ind`. La recomendación es no
hacerlo ahora, y escribir un ADR propio si se quiere Gödel I sobre Q++.

### 6 · La recomendación, y lo que decide el propietario

1. **¿R en lugar del verificador parametrizado de ADR‑137 §1?** Recomendado. Cumple el enunciado de ADR‑137 sin
   tocar los 142, V₀, G, el ancla ni el modelo, y su base ya compila y es pura (T08).
2. **¿Y si alguna vez se construye un verificador con parámetro?** Recomendado V‑B, no V‑A: es aditivo y deja intacto
   lo de T.
3. **¿Se aplazan las variantes de reglas?** Recomendado: sí.

**El orden después, con R:**
1. NegNum y PosNum de T. Es la pieza grande, y no cambia.
2. Pf_E y su transporte.
3. `rosser_ext`.
4. La Etapa 0 (`RosserReflexion`, `RosserBasura`) se porta a Pf_T.
5. La instancia de `rosser_ext` entra en `PUROS` (T08).

### 7 · Lo que NO cubre, y los riesgos

* **No mide el radio de compilación de V‑B** (dos axiomas más en la lista). Sólo hace falta si se elige V‑B.
* **La presentación cambia con R.** El predicado de R es el de T aplicado a `impChain`: otra presentación de T+E que la
  de un verificador que admitiera las líneas de E como axiomas. Para Rosser da igual. Para Gödel II de las extensiones
  importa (Feferman), y queda fuera de este alcance.
* **`hE` es imprescindible:** `PrfH E` es T+E sólo si E son sentencias. ✏️ *(2026‑10‑18, [ADR‑157](#adr-157))*: para
  la LECTURA; la prueba no la usa (ADR‑157 §2). Y es «si», no «sólo si»: con E = [#0 = #0], abierta, `PrfH E` es T.
* **El orden de `impChain`:** la cabeza de E va más adentro. Es una convención, que la sentencia de Rosser tiene que
  respetar.
* **T68:** retirar los 22 `ax_vpf_*` (G7: 50 declaraciones en 5 ficheros) es independiente de este diseño. Con R no
  hace falta. Con V‑B convendría hacerlo en el mismo cambio de valor de V₀.

**Véase también:** ADR‑117 (el ancla y F1), ADR‑134 (la inducción de los titulares), ADR‑137 (la decisión de Rosser),
ADR‑140 (las variantes) y ADR‑143 (T08); T01, T62, T64 y T68 de la auditoría.

## ADR-145: 🧭 Las decisiones del propietario sobre ADR‑144: Rosser por REDUCCIÓN (R); V‑B si alguna vez hace falta un verificador con parámetro; las variantes de reglas, aplazadas

**Fecha:** 2026-10-16 · **Estado:** ✅ decidido (este commit) · **Ámbito:** el estado de ADR‑137 y de ADR‑144;
`TEOREMAS-E-HIPOTESIS.md` (el banner y la fila de Rosser); `doc/AUDITORIA-SUELO-2026-10-12.md` (las decisiones, T01,
T62); `NEXT-STEPS.md`.

### 1 · Las decisiones

1. **Rosser por REDUCCIÓN (R)**, en lugar del verificador parametrizado de ADR‑137 §1. El enunciado de ADR‑137 sigue,
   con `PrfH E` en lugar de `PrfL (axioms ++ E)`:
   `rosser_ext (E) (hE : ∀ φ ∈ E, IsSentence φ) (hcon : ¬ PrfH E ⊥) : ¬ PrfH E (R E) ∧ ¬ PrfH E (neg (R E))`.
   El predicado de prueba de T+E se define con el de T: Pf_E(y, x) := Pf_T(y, `impChainC E x`).
2. **Si alguna vez hace falta un verificador con parámetro**, V‑B, el ADITIVO, y no V‑A. Haría falta para las
   variantes de reglas, o para Gödel II de las extensiones con su presentación propia.
3. **Las variantes de reglas** (Q++, PA, HA), aplazadas.

### 2 · Las consecuencias

* **No cambian** los 142, el verificador, V₀, el ancla, G ni el modelo.
* **T62 se cierra.** Parametrizar `Prf` por la teoría no hace falta para Rosser (ADR‑144 §3); si algún día hace falta
  un verificador con parámetro, será V‑B.
* **El orden:**
  1. NegNum y PosNum de T. Es la pieza grande, y va por la ruta sintáctica, para que T08 acepte la instancia.
  2. Pf_E y el transporte: PosNum_E y NegNum_E son los de T sobre `impChain E φ`.
  3. `rosser_ext`.
  4. Su instancia entra en `PUROS` (`Meta/PurezaTitulares.lean`) y tiene una fila en `TEOREMAS-E-HIPOTESIS.md`.
  ✏️ *(2026‑10‑18, [ADR‑157](#adr-157))*: 2, 3 y 4, hechos.
* **La Etapa 0 se reutiliza donde no usa el modelo.** `RosserBasura` §1–§4 es neutral. `RosserReflexion` pasa por
  `prf_sound` (ADR‑124), y queda como medida y como mutante con el que ver fallar T08. T64 sigue abierto, como parte
  de NegNum.
* **La base del paso 2** ya está en el árbol: `sondeos/ExtensionPorReduccion.lean`, un sondeo de CONTROL.

**Véase también:** ADR‑137, ADR‑143 y ADR‑144; T01, T62 y T64 de la auditoría.

## ADR-146: 🧭 El diseño de NegNum y PosNum de T, la pieza grande de Rosser: qué existe (76 de 80 piezas del build, PURAS), qué falta, y en qué orden, por la ruta SINTÁCTICA

**Fecha:** 2026-10-16 · **Estado:** 🟡 PROPUESTO; decide el propietario (§7). ✏️ *(2026‑10‑17, [ADR‑147](#adr-147))*: ✅
ACEPTADO en sus tres puntos, tal como se recomendaban · **Ámbito:** `sondeos/InventarioRosser.lean`
(la medición de pureza, de REGISTRO), `doc/registro/2026-10-16-negnum-posnum/` (la salida y los tres inventarios),
`sondeos/README.md`, `doc/registro/README.md`, `doc/AUDITORIA-SUELO-2026-10-12.md` (T01, T64, T66, T75),
`NEXT-STEPS.md` y la fila de Rosser de `TEOREMAS-E-HIPOTESIS.md`. Es el plan versionado que pedía T01: el de
`resultado.json` (ADR‑122) sólo vivía en un registro.

### 1 · Lo que Rosser necesita, enunciado

Con la reducción de ADR‑144/145, todo lo de T+E sale de T. De T hacen falta tres cosas, además del lema diagonal, que
ya existe:

```lean
def PfF (y x : Term) : Formula := land (chainOk nil y) (In x (runFn nil y))      -- el predicado de prueba de T
def ProofN (m y : Nat) : Prop :=                                                 -- su espejo en ℕ
  chainOkN (codeNatList axioms) 0 m ∧ memN y (runFnN 0 m)
theorem posNum {φ} (h : Prf φ) : ∃ m : Nat, Prf (PfF (numeralM m) (formCode φ))
theorem negNum (m y : Nat) (h : ¬ ProofN m y) : Prf (neg (PfF (numeralM m) (numeralM y)))
theorem w1Ax {m y : Nat} (h : ProofN m y) : Prf (dec y)                          -- W1, sin el modelo
```

* **El espejo se escribe con `codeNatList axioms`, no con `V₀`.** `V₀ = codeNatList axioms` sólo se demuestra por la
  solidez (`V₀_eq_codigo`), y T08 lo rechazaría. `ModeloCodigo` es aritmética sobre `Nat` y T08 lo admite.
* **Por qué hace falta W1.** La mitad ⊬R de Rosser usa que NINGÚN numeral es prueba de ¬R, y eso sólo sale de ¬Prf
  ¬R por la contrapositiva de W1: `ProofN m ⌜¬R⌝ → Prf ¬R`. Por eso NegNum' (¬Prf φ ⇒ ∀m, Prf ¬PfF(m̄, ⌜φ⌝)) es
  `negNum ∘ w1Ax`. La otra mitad, igual.
* **PosNum no necesita el espejo:** basta con que el código de prueba sea un numeral.

### 2 · La medición: qué existe y si es PURO (MEDIDO, `sondeos/InventarioRosser.lean`, 23 s)

Las 92 piezas que nombran el plan de Rosser y los tres inventarios del día, clasificadas por el recorrido de T08 (la
salida, en `doc/registro/2026-10-16-negnum-posnum/pureza.txt`):

| | piezas | qué son |
|---|---|---|
| **PURAS** | 76 | todo lo del build que el plan reutiliza: D1 y su seguimiento de cadenas, la evaluación de códigos canónicos a numeral, los refutadores de `CodeWitnessPrf`, las proyecciones a las guardas, `prf_ancla`, `prf_diagonal`, `prf_bdAll_numeral`, `prf_lt_trichotomy`, y de W1 todas las líneas salvo una |
| **IMPURAS** | 4 | `verificador_solido` (W1), `cadena_buena`, `linea_buena` y `linea_thy`. Las cuatro, por UN camino: `linea_thy ⟶ V₀_eq_codigo ⟶ evalFormula` |
| **FUERA del build** | 12 | las de los sondeos: `RosserBasura` §1–§4 (sin el modelo, por lectura), `RosserReflexion` (con el modelo) y `ExtensionPorReduccion` (PURA, por su `#pureza`) |

⇒ **La ruta sintáctica no tiene que reescribir nada de lo que hay.** Todo lo reutilizable del build es puro, y lo único
impuro, W1, lo es por un solo lema, que se sustituye enunciándolo con `codeNatList axioms`. Los tres inventarios, con
fichero:línea, están en la misma carpeta.

### 3 · Qué existe y qué falta, por etapa (las del plan de ADR‑122, adaptadas a la ruta P y a la reducción)

| etapa | qué da | qué existe (puro) | qué falta |
|---|---|---|---|
| **W1(ax)** | `w1Ax` | todas las líneas de W1 salvo `linea_thy`; `memN_codeNatList`, `dec_codeNat` | `linea_thy` con `codeNatList axioms` y la cadena con V como parámetro |
| **6 · PosNum** | `posNum` | `repr_pos'_prf`, que construye un TÉRMINO de prueba explícito (`proofCode' rs []`) y prueba sus dos mitades; `prf_formCode_numeral`, `prf_cons_eval` y `prf_cons_eval_of`; los transportes `prf_chainOk_subst2`, `prf_congr_runFn_2`, `prf_eq_subst_in` | UN lema: `Prf (proofCode' rs acc =eq numeral N)`, con un espejo `codeNatProof` de `proofCode'`; y el ensamblaje |
| **1 · la capa de listas sobre numerales** | descomponer, acceder, decidir `In` | `prf_cons_eval`, `prf_in_cons_iff`, `prf_not_in_nil`, `prf_in_concat_singleton_iff`, `crit_num_ne`, `prf_lt_numeralM`, `prf_objList_numeral`, `prf_lenc_objList`, `prf_nthc_objList` | `numeralM m = cons (carN m)‾ (cdrN m)‾`; los accesores y los constructores de código sobre numerales; `¬memN → Prf ¬In`; la pertenencia en `runFnN` |
| **2 · NumEval, la sustitución sobre numerales** | evaluar `substfc`/`liftfc`/`substtc`/`liftc` con guardas verdaderas | `prf_substTerm_arith`, `prf_liftTerm_arith`, `prf_substFormula_arith` y `prf_liftFormula_arith`, sólo sobre códigos CANÓNICOS | todo lo de numerales: el análogo de `ArithPrf.lean:181-473` sobre códigos de `Nat`, con la clausura de las guardas en ℕ |
| **3 · GuardNeg** | `¬hasWitN c → Prf ¬hasWit c̄`, y lo mismo para `hasWitF` | los refutadores de profundidad 1 de `CodeWitnessPrf` y las herramientas del paso hereditario (`prf_isTermCodeE1_of_In`, `prf_isFormCodeE2_of_In`, `PrfH_inst_argsIn`); `RosserBasura` §1–§4, de profundidad 2 y sólo para `hasWit` | la caracterización en ℕ (construir el testigo), la hereditaria GENERAL (inducción en el numeral) para `hasWit`, y TODO `hasWitF` (∃∃, ocho cláusulas, recursión mutua) |
| **4 · NegLineWF** | `¬lineWFT Vax K x → Prf ¬lineWF x̄`, por etiqueta | `prf_lineWF_inv`, `prf_of_tagDisj`, `pcc_tag_vacuous`, `prf_lineWF_neg_of_tag` (19 etiquetas estructurales, sobre líneas explícitas), las 21 `prf_lenc_<tag>` de `ChainNegPrf`, `prf_lineWF_thy`, `prf_ancla`; 3 de las 11 proyecciones a las guardas | pasar de líneas explícitas a numerales (etapa 1); las 7 etiquetas de sustitución (etapa 2); las 8 proyecciones que faltan; `thy`: la contraria de `memN_codeNatList` y `¬In` sobre `listFormCodeM` |
| **5 · NegChain y NegNum** | `negNum`, y NegNum' con W1(ax) | `prf_chainOk_cons`, `prf_allIn_cons`, `prf_chainOk_iff_chainOkB`, `prf_lineWF_of_chainOk`, `prf_boundedPremsIn_of_chainOk` (✏️ retirado con `ChainNegPrf` en ADR‑160: NegNum no lo usó), `prf_In_runFn_iff` | la «primera línea mala» en ℕ, las premisas (`¬allInN`), el ensamblaje |
| **7 · Rosser, por la reducción** | `rosser_ext` | `prf_diagonal`, `prf_bdAll_numeral`, `prf_lt_trichotomy`, `prf_lt_succ_split`, `liar_isSentence`; `prfH_iff_prf_impChain` y `formCode_impChain` (sondeo) | el caso `z ≤ n̄`; Pf_E y su transporte; la sentencia R y `IsSentence R`; el argumento |

### 4 · El diseño

1. **Un espejo, dos sentidos.** Cada símbolo del verificador tiene su espejo en ℕ en `ModeloCodigo` (`memN`, `allInN`,
   `premsOfN`, `runFnN`, `lineWFT`, `chainOkL`, `hasWitN`, `hasWitFN`, `substfcN`…). NegNum se construye de abajo
   arriba como «T decide el espejo sobre numerales». Cada nivel da el sentido positivo (evaluar) y el negativo
   (refutar lo falso): listas → sustitución → guardas → líneas → cadenas → `PfF`. Es la organización del plan de
   ADR‑122, dicha como un solo juicio por símbolo.
2. **PosNum, por D1.** No por el espejo: el término que D1 ya construye es un árbol de numerales, y basta probar que es
   igual a un numeral. Es la etapa más barata, y la única que no depende de las demás.
3. **W1(ax) primero.** Es un lema, y desbloquea NegNum'.
4. **La guarda de fórmulas, pronto.** GuardNeg es lo de más riesgo («medio‑alto»: ∃∃, ocho disyuntos, recursión
   mutua término/fórmula), y de `hasWitF` no hay nada. Un sondeo de `hasWitF` a profundidad 1–2 va justo después de
   la etapa 1, antes de invertir en las etapas 2 y 4.
5. **En el build, con T08 en cada módulo.** Los módulos van en el build (`Meta/RosserW1.lean`,
   `Meta/RosserPosNum.lean`, `Meta/RosserNumerales.lean`, `Meta/RosserNumEval.lean`, `Meta/RosserGuardNeg.lean`,
   `Meta/RosserNegLinea.lean`, partido si hace falta, `Meta/RosserNegNum.lean` y `Meta/Rosser.lean`). Cada uno acaba
   con un `#pureza` de sus resultados, así que un paso por el modelo rompe el build en el módulo que lo da. Al final,
   la instancia de `rosser_ext` entra en `PUROS` y en `T_UNIVERSO`.
6. **Se promueve lo que sirve.**
   - `RosserBasura` §1–§4 pasa a las etapas 1 y 3. El sondeo se queda con §5, su control con el modelo. ✏️ *(2026‑10‑18,
     [ADR‑160](#adr-160))*: hecho.
   - `ExtensionPorReduccion` pasa a `Meta/Rosser.lean`.
   - `RosserReflexion` se queda como mutante de T08.
   - De `ChainNegPrf` se usan en su sitio las 21 `prf_lenc_<tag>`, `prf_lineTag_cons` (✏️ retirados en ADR‑160) y
     `prf_boundedPremsIn_of_chainOk` (retirado también). Lo demás se decide al final (T66), midiendo con el cono qué usó NegNum.
     ✏️ *(2026‑10‑18, [ADR‑160](#adr-160))*: NegNum no usó ninguno; `ChainNegPrf` salió entero del build.
7. **Las reglas del núcleo, desde el primer día:** lemas ∀ y `rw`; nunca `simp`, `rfl` ni `decide` sobre un código
   cerrado, el ancla o ⌜R⌝; `unfold` e inducción funcional en las recursiones mutuas (ADR‑130); el despacho por
   etiqueta, partido en módulos por la memoria.

**Controles de cada etapa:**
* el `#pureza` del módulo;
* que la hipótesis de `negNum` pueda fallar: para el código de una prueba de un axioma, `ProofN` vale;
* y que pueda valer: `¬ ProofN 0 y`, la cadena vacía.

### 5 · Las cifras (ESTIMACIÓN, del plan; ninguna medida mía)

| etapa | ESTIMACIÓN | fuente |
|---|---|---|
| W1(ax) | 15–30 | `resultado.json` (crítica), T75 |
| 6 · PosNum | 70–120 (40–80 según la crítica) | `resultado.json:270`; informe de T01 |
| 1 · listas | 150–250 | `resultado.json:238-241` |
| 2 · NumEval, ruta P | 350–600 | `resultado.json:244-247` |
| 3 · GuardNeg | 350–550, y 60–150 más por la caracterización en ℕ | `resultado.json:250-253`; crítica §ROSSER 1.4 |
| 4 · NegLineWF | 450–650 (las proyecciones, unas 96) | `resultado.json:256-259` |
| 5 · NegChain y NegNum | 150–250 | `resultado.json:262-265` |
| 7 · Rosser, con la reducción | 200–400 | ADR‑144 |
| **suma** (mía) | **≈ 1 800–3 000** | la suma de las filas; el informe de T01 daba ≈ 1 710–2 850 sin la reducción ni W1 |

**La calibración, MEDIDA:**
* W1 se estimó en 600–1 500 líneas y salieron unas 490.
* La Etapa 0 se estimó en 120–200 y lleva 406 líneas de fichero (194 de declaraciones) con dos de sus tres piezas.

Las cifras del plan valen, por tanto, a un factor 2 en cada sentido. **La unidad,** que el plan no fijaba: las líneas no
vacías tras `strip-lean.awk`, medidas al cerrar cada etapa contra su estimación.

### 6 · Los riesgos (del plan y de los inventarios)

1. **GuardNeg** (§4.4). Que sea inevitable lo argumenta un razonamiento de modelo no compilado: los 142 axiomas no
   fijan `substfc` en una ranura basura. T75(d) propone un segundo modelo como prueba.
2. **Los numerales astronómicos** (⌜R⌝, el ancla, `tcFnN 0` ≈ 2,4·10¹¹; la trampa de ADR‑124, más de 14 GB con un
   `simp … at h` sobre códigos cerrados) y **el núcleo con las mutuas** (ADR‑130).
3. **Los precedentes, rotos o con el signo cambiado:** los refutadores de `hasWitF` están archivados y no compilan, y
   los de q1 son de antes de las guardas.
4. **T08 mira por espacio de nombres**, y se aplica a la INSTANCIA, no a un enunciado con hipótesis (`rosser_de`).
5. **Las estimaciones** (§5).

### 7 · Lo que decide el propietario

1. **¿El orden de §4?** W1(ax) → PosNum → las listas → un sondeo de `hasWitF` (riesgo primero) → NumEval → GuardNeg →
   NegLineWF → NegNum → Rosser por la reducción. Recomendado.
2. **¿En el build, con un `#pureza` por módulo, o en sondeos que se promueven al final?** Recomendado: en el build.
3. **¿T66 (retirar lo que sobre de `ChainNegPrf` y del subárbol sin consumidor) se decide al final, midiendo qué usó
   NegNum?** Recomendado.

**Lo que NO cubre:** el código. Ninguna etapa está empezada aquí, y las cifras son las del plan.

**Véase también:** ADR‑122 §2 (el plan), ADR‑123…127 (la Etapa 0), ADR‑130 (el núcleo), ADR‑143 (T08), ADR‑144 y
ADR‑145 (la reducción); T01, T64, T66 y T75 de la auditoría.

## ADR-147: 🧭 Las decisiones del propietario sobre ADR‑146: el orden de su §4, con el riesgo de `hasWitF` pronto; el código en el build, con un `#pureza` al final de cada módulo; T66, al final

**Fecha:** 2026-10-17 (la respuesta del propietario es del 2026‑10‑16, 22:08) · **Estado:** ✅ decidido (este commit) ·
**Ámbito:** el estado de ADR‑146; `TEOREMAS-E-HIPOTESIS.md` (la fila de Rosser); `doc/AUDITORIA-SUELO-2026-10-12.md`
(las decisiones, T01, T64, T66 y T75); `NEXT-STEPS.md`.

### 1 · Las decisiones

El propietario respondió a las tres preguntas de ADR‑146 §7 (entre comillas, sus palabras):

1. **El orden de §4**, «con el riesgo temprano de `hasWitF`»: W1(ax) → PosNum → la capa de listas → un sondeo de
   `hasWitF` → NumEval → GuardNeg → NegLineWF → NegNum → Rosser por la reducción.
2. **En el build:** «el código va en el build, con un `#pureza` al final de cada módulo». Cada etapa es un módulo de
   `Meta/` (los nombres de ADR‑146 §4, punto 5) que acaba con el `#pureza` de sus resultados, así que un paso por el
   modelo rompe el build en el módulo que lo da.
3. **T66, al final:** «lo que sobre de `ChainNegPrf` (T66) se decide al final, midiendo qué ha usado NegNum».

Son las tres opciones que ADR‑146 recomendaba.

### 2 · Por qué se registra el 17

La respuesta se escribió el 2026‑10‑16 a las 22:08, en la sesión que había preparado ADR‑146, y no llegó a
procesarse: Claude Code devolvió un error de acceso y la sesión no siguió. Se recupera de su transcripción y se
registra al día siguiente, a petición del propietario. Entre las dos fechas el árbol no cambió (`master` = `0640c52`).

### 3 · Las consecuencias

* **ADR‑146 pasa a ✅ aceptado.** Sus §3 (qué existe y qué falta), §4 (el diseño) y §6 (los riesgos) son el plan
  vigente. Las cifras de su §5 siguen siendo ESTIMACIÓN; cada etapa se mide al cerrarse, en líneas no vacías tras
  `strip-lean.awk`.
* **Lo siguiente, W1(ax):** `w1Ax`, con `codeNatList axioms` en lugar de `V₀`, en `Meta/RosserW1.lean` y con su
  `#pureza`. Sus controles son los de ADR‑146 §4: la hipótesis de la etapa puede valer y puede fallar.
* **El sondeo de `hasWitF`** va justo después de la capa de listas. Es la puerta del riesgo: su resultado se registra
  antes de invertir en NumEval y NegLineWF.
* **T66 sigue abierto** hasta el final de NegNum. Se decide con el cono (`sondeos/ConoTitulares.lean`) sobre lo que
  NegNum haya usado.
* **No cambian** los 142, el verificador, V₀, el ancla, G ni el modelo, ni la línea de llegada (ADR‑140).

**Véase también:** ADR‑144, ADR‑145 y ADR‑146; T01, T64, T66 y T75 de la auditoría.

## ADR-148: 🔧 Rosser, etapa W1(ax): `w1Ax`, W1 con el código de los 142 y SIN el modelo (`Meta/RosserW1.lean`); la cadena de W1, paramétrica en `V`

**Fecha:** 2026-10-17 · **Estado:** ✅ hecho (este commit) · **Ámbito:** `Meta/SolidezVerificador.lean` §4 (la cadena,
paramétrica), `Meta/RosserW1.lean` (nuevo), `Meta.lean`, `check-footprints.bash` (tres filas), `REFERENCE.md` (84x,
84z y la cifra de módulos), `doc/REFERENCE-Incompleteness.md` y `CURRENT-STATUS-PROJECT.md` (las cifras),
`TEOREMAS-E-HIPOTESIS.md` (el banner y la fila de Rosser), `NEXT-STEPS.md` y `doc/AUDITORIA-SUELO-2026-10-12.md`
(T01, T75). Es la primera etapa del plan de ADR‑146, en el orden y la forma de ADR‑147.

### 1 · Qué se hizo

1. **La cadena de W1, paramétrica en `V`.** En `SolidezVerificador` §4, las 21 `linea_*`, `linea_buena` y
   `cadena_buena` valen para cualquier `V`. La regla `thy` pide `Bueno V`, que todo lo que hay en `V`, decodificado,
   sea teorema: `linea_thy (hV : Bueno V) (hT : lineWFT V 15 x) := hV _ hT.2`. Hay dos instancias:
   * `bueno_codeNatList : Bueno (codeNatList axioms)`, por `memN_codeNatList`, `dec_codeNat` y `Prfᵢ.thy`, sin el
     modelo;
   * `bueno_V₀ : Bueno V₀`, por `V₀_eq_codigo`, que es la solidez. Es ahora el ÚNICO paso de W1 por el modelo.

   `verificador_solido` conserva su enunciado (`chainOkN V₀ 0 p`) y su footprint: lo prueba la cadena con `bueno_V₀`.
2. **`Meta/RosserW1.lean`.** `ProofN m y := chainOkN (codeNatList axioms) 0 m ∧ memN y (runFnN 0 m)`, el espejo de
   ADR‑146 §1, y `w1Ax : ProofN m y → Prf (dec y)`, que es la cadena con `bueno_codeNatList`.

### 2 · Lo medido

* **T08**, el `#pureza` del módulo, que corre en cada build: `w1Ax`, `proofN_axioma`, `w1Ax_axioma` y
  `not_proofN_zero` son PUROS (cierres de 635, 475, 486 y 432 constantes del proyecto). El control positivo,
  `verificador_solido`, sale IMPURO, por `bueno_V₀ ⟶ V₀_eq_codigo ⟶ evalFormula`. ✏️ *(el mismo día,
  [ADR‑149](#adr-149))*: esos cierres son de un recorrido que no seguía los lemas del propio módulo; con el recorrido
  completo son 636, 479, 655 y 433, y el veredicto es el mismo.
* **Los footprints:** los tres nuevos, `[propext, Quot.sound]`; los de `SolidezVerificador`, sin cambios.
  `check-footprints`: 495 cuadran, y [COBERTURA], 466 de 466.
* **Los controles de ADR‑146 §4.** La hipótesis puede valer: `proofN_axioma`, la cadena de una línea `thy` que cita un
  axioma; con `w1Ax` da `w1Ax_axioma : a ∈ axioms → Prf a`. Y puede fallar: `not_proofN_zero`, la cadena vacía no
  concluye nada.
* **Lo que cambia en la medición de ADR‑146 §2:** `cadena_buena` y `linea_buena` pasan de IMPURAS a PURAS, y la
  impureza de W1 queda sólo en `bueno_V₀` (`linea_thy` ya no la tiene). `doc/registro/2026-10-16-negnum-posnum/pureza.txt`
  es el registro del 2026‑10‑16 y no se toca.
* **Las líneas**, en la unidad de ADR‑147 (no vacías tras `strip-lean.awk`, con `LC_ALL=C`): `ProofN` y `w1Ax`, 3;
  `SolidezVerificador`, de 470 a 473; los controles, 30; el módulo entero, 47. La ESTIMACIÓN de ADR‑146 §5 era 15–30.
* **El build:** 131 jobs (antes 130) y 114 módulos; `RosserW1` compila en 3,3 s; los 12 sondeos de control compilan
  y no hay ningún aviso nuevo.

### 3 · Las consecuencias

* **Lo siguiente, PosNum** (ADR‑146 §3, etapa 6): `posNum`, por D1 y un lema, `Prf (proofCode' rs acc =eq numeral N)`,
  con un espejo `codeNatProof` de `proofCode'`.
* **NegNum'** será `negNum` seguido de `w1Ax` (ADR‑146 §1).
* **Una nota para la etapa 7.** Los módulos de Rosser importan `PurezaTitulares` para usar `#pureza`. Cuando la
  instancia de `rosser_ext` entre en `PUROS`, ese fichero no podrá importar `Meta/Rosser.lean` sin crear un ciclo, y
  habrá que llevar el comando, o la lista `PUROS`, a un módulo aparte. Hoy no hace falta. ✏️ *(2026‑10‑18,
  [ADR‑157](#adr-157))*: hecho así: el recorrido y el comando, a `Meta/PurezaComando.lean`.

**Véase también:** ADR‑121 (W1), ADR‑143 (T08), ADR‑146 (el diseño) y ADR‑147 (las decisiones); T01 y T75 de la
auditoría.

## ADR-149: 🔧 Rosser, etapa 6, PosNum: `posNum`, D1 con el testigo en forma de NUMERAL (`Meta/RosserPosNum.lean`); y T08 sigue por fin los lemas del propio módulo

**Fecha:** 2026-10-17 · **Estado:** ✅ hecho (este commit) · **Ámbito:** `Meta/RosserPosNum.lean` (nuevo),
`Meta/PurezaTitulares.lean` (el recorrido y su control), `Meta.lean`, `check-footprints.bash` (dos filas),
`REFERENCE.md` (84y, 84za y la cifra de módulos), `doc/REFERENCE-Incompleteness.md` y `CURRENT-STATUS-PROJECT.md` (las
cifras), `TEOREMAS-E-HIPOTESIS.md` (el banner, §0 y la fila de Rosser), `NEXT-STEPS.md`,
`doc/AUDITORIA-SUELO-2026-10-12.md` (T01 y T08) y una nota en ADR‑148 §2. Es la segunda etapa del orden de ADR‑147.

### 1 · PosNum

1. **El espejo en ℕ del codificador de pruebas:** `codeNatJustif`, `codeNatLine` y `codeNatProof`, copia de
   `Meta/Representability2.lean:60-95`.
2. **El lema que faltaba** (ADR‑146 §3): `prf_proofCode'_numeral : Prf (proofCode' rs acc =eq numeral (codeNatProof rs acc))`.
   Sale de `prf_lineJustif_numeral` (las 21 reglas) y `prf_lineCode'_numeral`, por inducción sobre las reglas, con el
   esqueleto de `prf_runFn_track`. Las hojas las daban `prf_formCode_numeral` y `prf_termCode_numeral`.
3. **`PfF y x := land (chainOk nil y) (In x (runFn nil y))`** (ADR‑146 §1) y **`posNum : Prf φ → ∃ m, Prf (PfF m̄ ⌜φ⌝)`**,
   con el testigo explícito en `posNum_de` (`m = codeNatProof rs []`). Las dos mitades de D1 (`prf_chainOk_track`,
   `prf_In_runFn_of_mem`) se transportan por la igualdad (`prf_chainOk_subst2`, `prf_congr_runFn_2`, `prf_eq_subst_in`).
4. **Los controles:** `prov_of_pfF` (`PfF` es la matriz de `provCodeC'`: un testigo da `Prov(⌜φ⌝)`) y `repr_pos_num`
   (con `posNum`, D1 otra vez: el enunciado de PosNum no dice menos que D1).

### 2 · T08 no seguía los lemas del propio módulo

* **Lo que pasaba.** `delProyecto` decidía si una constante es del proyecto por su módulo de importación. Las del
  fichero que se compila no tienen (`getModuleIdxFor?` da `none`) y se descartaban. A `#pureza_titulares` no le afecta,
  porque sus titulares son importados. Pero el `#pureza` al final de un módulo, que es lo que decidió ADR‑147, no
  recorría los lemas del propio módulo.
* **Cómo se vio.** Por la medición, no por el veredicto: el cierre de `posNum` (476 constantes) salía menor que el de un
  lema que usa, `prf_proofCode'_numeral` (613), y eso es imposible si el recorrido es completo.
* **Medido con un mutante** (en el scratchpad de la sesión): una raíz que sólo nombra un lema del mismo fichero, y ese
  lema llama a `consistencia`. Salía PURO. Con el arreglo dispara:
  `raizMutante ⟶ auxSemantico ⟶ consistencia ⟶ consistentH_de`.
* **El arreglo:** `delProyecto` cuenta también las constantes del fichero en curso (`env.contains n`). Queda vigilado en
  cada build: `mutanteLocal`, al final de `PurezaTitulares`, es un control positivo con la forma del mutante. Si el
  recorrido volviera a quedarse ciego, saldría puro y el build no compilaría.
* **Qué cambia.** Los 8 titulares, nada: los mismos cierres. RosserW1: los cuatro siguen PUROS, con cierres de 636, 479,
  655 y 433 (fe de erratas de ADR‑148 §2, que daba 635, 475, 486 y 432). `ExtensionPorReduccion`, un sondeo de CONTROL
  que usa `#pureza` sobre sus propios lemas, sigue compilando con el recorrido completo.

### 3 · Lo medido

* **T08:** `prf_proofCode'_numeral`, `posNum` y `repr_pos_num` son PUROS (cierres de 636, 1 063 y 1 068 constantes del
  proyecto). El control positivo, `modelo_prov_iff`, que es D1 leído en el modelo, sale IMPURO.
* **Los footprints:** `posNum` y `repr_pos_num`, `[propext, Classical.choice, Quot.sound]`, los de D1 (T11b).
  `prf_proofCode'_numeral`, `[propext, Quot.sound]`, medido al compilar. No tiene fila porque [COBERTURA] extrae los
  nombres con `'[^']+'` y la prima lo corta, como a `repr_pos'_prf`. `check-footprints`: 497 cuadran; [COBERTURA], 468
  de 468.
* **Las líneas**, en la unidad de ADR‑147: el espejo, 29; los lemas de numeral, 58; `PfF` y `posNum`, 12; los
  controles, 4; el módulo entero, 120. `PurezaTitulares`, de 112 a 116. La ESTIMACIÓN de ADR‑146 §5 era 70–120 (40–80
  según la crítica).
* **El build**, el 2026-10-17: 132 jobs y 115 módulos; `RosserPosNum` compila en 3,5 s; los 12 sondeos de control compilan y no hay
  ningún aviso nuevo.

### 4 · Las consecuencias

* **Lo siguiente:** la capa de listas sobre numerales (ADR‑146 §3, etapa 1) y, justo después, el sondeo de `hasWitF`.
* **`PfF` es el predicado** con el que se escribirá la sentencia de Rosser. Su lema de sustitución (`PfF` bajo
  `substFormula`) va con la etapa 7.
* **Una lección para los controles:** un control que se usa en un sitio nuevo hay que volver a verlo fallar allí.
  T08 se vio fallar en ADR‑143 con titulares importados, y el uso por módulo de ADR‑147 era otro caso.

**Véase también:** ADR‑143 (T08), ADR‑146 (el diseño), ADR‑147 (las decisiones) y ADR‑148 (W1(ax)); T01 y T08 de la
auditoría.

## ADR-150: 🔧 Rosser, etapa 1: la capa de listas sobre numerales (`Meta/RosserNumerales.lean`): descomponer, acceder, decidir `In` y evaluar `runFn`

**Fecha:** 2026-10-17 · **Estado:** ✅ hecho (este commit) · **Ámbito:** `Meta/RosserNumerales.lean` (nuevo),
`sondeos/RosserBasura.lean` (tres lemas, promovidos) y su fila en `sondeos/README.md`, `Meta.lean`,
`check-footprints.bash` (seis filas), `REFERENCE.md` (84zb y la cifra de módulos), `doc/REFERENCE-Incompleteness.md` y
`CURRENT-STATUS-PROJECT.md` (las cifras), `TEOREMAS-E-HIPOTESIS.md` (el banner y la fila de Rosser), `NEXT-STEPS.md` y
`doc/AUDITORIA-SUELO-2026-10-12.md` (T01 y T64). Es la tercera etapa del orden de ADR‑147.

### 1 · Qué se hizo

Sobre un numeral `m̄`, `Prf` hace lo que hace ℕ con el espejo de `ModeloCodigo`:

1. **Descomponer:** `prf_cons_evalM` y `prf_numeral_cons`, un numeral no nulo es un `cons`:
   `m̄ = cons ⟨carN m⟩‾ ⟨cdrN m⟩‾`.
2. **Acceder:** `prf_carc_numeral` y `prf_cdrc_numeral` (con `m ≠ 0`), `prf_lenc_numeral` (todo `m`) y
   `prf_nthc_numeral` (con `i < lenN m`). Fuera de esas condiciones los axiomas no fijan `carc` ni `nthc` sobre `nil`, y no
   se afirma nada.
3. **Los constructores de código de fórmula:** `prf_implc_numeral : implc ā b̄ = ⟨implcN a b⟩‾`, y los de `⊥`, `=`, `∀`,
   `∧`, `∨` y `∃`.
4. **Decidir `In`:** `prf_In_numeral` (`memN y l → Prf (In ȳ l̄)`) y `prf_not_In_numeral` (`¬ memN y l → Prf ¬(In ȳ l̄)`),
   por inducción sobre la lista, con `prf_in_cons_iff` y `crit_num_ne`.
5. **`concat` y `runFn`, evaluados:** `prf_concat_numeral` y `prf_runFn_numeral`, éste con la hipótesis de que ninguna
   línea es `0`, porque sobre `0` `carc` no está fijado. Con ellos, la pertenencia a las conclusiones de una cadena,
   decidida: `prf_In_runFn` y `prf_not_In_runFn`. Su lado ℕ: `runFnL_eq` y `memN_runFnN_zero` (las conclusiones son las
   cabezas de las líneas).
6. **La promoción** (ADR‑146 §4.6): `prf_cons_evalM`, `prf_congr_carc` y la etiqueta de `⟨k, r⟩‾` (`prf_carc_consN`)
   vienen de `RosserBasura` §3–§4. El sondeo los usa ahora desde el build; lo que le queda de §1–§4, la guarda, es de
   la etapa 3.

### 2 · Lo medido

* **T08:** los 13 resultados del `#pureza` son PUROS (cierres de 526 a 601 constantes del proyecto). El control
  positivo, `ev_numeralM` (el valor de un numeral en el modelo), sale IMPURO.
* **Los footprints:** los seis impresos, `[propext, Quot.sound]`. `check-footprints`: 503 cuadran; [COBERTURA], 474 de 474.
* **El control** `prf_In_decide`: para todo par de numerales, `Prf` prueba la pertenencia o la refuta.
* **Las líneas**, en la unidad de ADR‑147: §1, 13; §2, 37; §3, 18; §4, 27; §5, 48. En total, 143, y 5 del control; el
  módulo entero, 175. `RosserBasura`, de 116 a 102. La ESTIMACIÓN de ADR‑146 §5 era 150–250.
* **El build**, el 2026-10-17: 133 jobs y 116 módulos; `RosserNumerales` compila en 11 s, a la primera; los 12 sondeos de control
  compilan, `RosserBasura` incluido, y no hay ningún aviso nuevo.

### 3 · Las consecuencias

* **Lo siguiente, el sondeo de `hasWitF`** (ADR‑147): la puerta del riesgo, a profundidad 1–2 sobre numerales, antes de
  invertir en NumEval y NegLineWF.
* **Lo que esta capa no cubre:** una cadena con alguna línea `0`, cuyo acumulador (`concat c [carc 0̄]`) no se evalúa.
  NegNum separa antes ese caso: las cadenas válidas no tienen líneas `0` (inventario de NegNum, G).

**Véase también:** ADR‑146 (el diseño), ADR‑147 (las decisiones) y ADR‑149 (PosNum y T08); T01 y T64 de la auditoría.

## ADR-151: 🔬 El sondeo de `hasWitF`, la puerta del riesgo de GuardNeg: la guarda de fórmula se refuta sobre numerales basura a profundidad 1 y 2, sin el modelo (`sondeos/RosserHasWitF.lean`)

**Fecha:** 2026-10-17 · **Estado:** ✅ hecho (este commit); la puerta, abierta · **Ámbito:** `sondeos/RosserHasWitF.lean`
(nuevo, de CONTROL), `sondeos/CONTROLES.txt`, `sondeos/README.md`, `TEOREMAS-E-HIPOTESIS.md` (la fila de Rosser),
`NEXT-STEPS.md` y `doc/AUDITORIA-SUELO-2026-10-12.md` (T01 y T64). Es el cuarto paso del orden de ADR‑147.

### 1 · La pregunta

GuardNeg es la etapa de más riesgo de Rosser (ADR‑146 §4.4 y §6.1, «medio‑alto»): la guarda de FÓRMULA es `∃∃`, tiene
ocho cláusulas y cruza la de términos, y de refutarla en `Prf` no había nada que compilara (los precedentes están
archivados y rotos). ADR‑147 pone este sondeo justo después de la capa de listas, antes de invertir en NumEval y
NegLineWF.

### 2 · Lo que dice (compilado, en `sondeos/RosserHasWitF.lean`)

* Profundidad 1, la etiqueta (`prf_neg_hasWitF_num`, en `sondeos/RosserHasWitF.lean`): `Prf (¬ hasWitF ⟨k, r⟩‾)` para
  todo `k ∉ {2,…,9}` y todo `r`.
* Profundidad 2, casilla de FÓRMULA (`prf_neg_hasWitF_impl`, en `sondeos/RosserHasWitF.lean`):
  `Prf (¬ hasWitF ⟨5, ⟨k, r⟩, b⟩‾)` para todo `k ∉ {2,…,9}`.
* Profundidad 2, casilla de TÉRMINO (`prf_neg_hasWitF_eq`, en `sondeos/RosserHasWitF.lean`):
  `Prf (¬ hasWitF ⟨4, ⟨k, r⟩, b⟩‾)` para todo `k ∉ {0, 1}`. La guarda de fórmula pasa aquí por la de términos.
* El control `control_codigo_no_refutable`: sobre el numeral del código de cualquier fórmula, `¬ hasWitF` no es
  demostrable (la solidez en `MNV V₀` y `prf_hasWitF_real`). No mide el método sino la guarda.

### 3 · Lo medido

* **Compila en 5 s**, con `lake lean`. Los tres resultados tienen footprint `[propext, Quot.sound]`. Su `#pureza`: PUROS
  (cierres de 620, 691 y 698 constantes del proyecto); el control, IMPURO.
* **Las líneas** (no vacías tras `strip-lean.awk`): 128 en total. §1, el `∃∃` e `isFC1`, 16; §2, las formas y dos
  selectores de cláusula, 44, de ellas 12 por selector; §3, la profundidad 1, 9; §4, la profundidad 2, 35; §5, el
  control, 9.
* **Lo que costó cada riesgo:**
  - El `∃∃`: dos `prf_ex_elim_imp`. No era un riesgo.
  - Las ocho cláusulas: un selector por etiqueta (`prf_E2_sel5` y `prf_E2_sel4`, en `sondeos/RosserHasWitF.lean`),
    que refuta las otras siete por la forma (`prf_shapeNul_str`, `prf_shapeUn_str'`, `prf_shapeBin_str'` y
    `crit_tag_absurd`).
  - El cruce término/fórmula: `wfAll1` y el rechazo de término que ya existía (`crit_isTermCodeB1_rejects`).
* Compiló tras dos arreglos de nombres: un `liftTerm_numeralM` ambiguo, y `prf_hasWitF_real` vive en `HW`.

### 4 · Lo que no mide, y la cifra

* **No mide** la versión hereditaria GENERAL (inducción sobre el numeral, con las ocho cláusulas en cada nivel), ni la
  caracterización en ℕ (construir el testigo cuando la guarda es verdadera), ni la etiqueta buena con forma mala, ni la
  casilla de lista de `atom` (`argsIn`), ni el `0`.
* **La ESTIMACIÓN de GuardNeg se mantiene** (ADR‑146 §5: 350–550 líneas, y 60–150 más por la caracterización en ℕ). El
  sondeo quita el riesgo del `∃∃` y de la selección, que era lo que peor se sabía hacer, pero no mide lo grande, la
  inducción general.

### 5 · Las consecuencias

* **La puerta del riesgo se abre.** Lo siguiente es NumEval (ADR‑146 §3, etapa 2), y GuardNeg después. Cuando GuardNeg
  entre en el build, los selectores se generalizan a las ocho etiquetas.
* **El sondeo es de CONTROL:** la CI lo compila en cada push (13 sondeos de control).

**Véase también:** ADR‑146 §4.4 y §6 (el riesgo), ADR‑147 (el orden) y ADR‑150 (la capa de listas que usa); T01 y T64
de la auditoría.

## ADR-152: 🔧 Rosser, etapa 2, NumEval: la sustitución sobre numerales con las guardas verdaderas (`Meta/RosserNumEval.lean`)

**Fecha:** 2026-10-17 · **Estado:** ✅ hecho (este commit) · **Ámbito:** `Meta/RosserNumEval.lean` (nuevo),
`Meta/NumCodeClosedPrf.lean` (dos congruencias de listas) y la nota de `Meta/CodeWitnessPrf.lean` que pedía ese sitio,
`Meta.lean`, `check-footprints.bash` (seis filas), `REFERENCE.md` (84zc y las cifras de módulos y de sondeos),
`doc/REFERENCE-Incompleteness.md` y `CURRENT-STATUS-PROJECT.md` (las cifras), `TEOREMAS-E-HIPOTESIS.md` (el banner y la
fila de Rosser), `NEXT-STEPS.md` y `doc/AUDITORIA-SUELO-2026-10-12.md` (T01 y T64). Es el quinto paso del orden de
ADR‑147.

### 1 · Qué se hizo

Sobre numerales, `Prf` evalúa la sustitución y el lift como sus espejos de ℕ (`substtcN`…`liftfcN`, en
`ModeloCodigo`), siempre que el código sea BUENO:

1. **Los códigos buenos en ℕ:** `CodT` y `CodTs` (término y lista de términos, mutuos) y `CodF` (fórmula): los árboles
   que forman los constructores de código, con cualquier número como código de símbolo. Sobre lo que no es un árbol, la
   «basura», no se afirma nada: los axiomas de la sustitución no llevan guarda y allí no la fijan (ADR‑146 §6.1).
2. **La clausura en ℕ:** `liftcN`, `substtcN`, `liftfcN` y `substfcN` llevan códigos buenos a códigos buenos
   (`codT_liftcN`, `codF_liftfcN`, `codF_substfcN`…). La de `liftcN` la usa el caso `∀`. La de `liftfcN` la pedirá
   NegLineWF, porque en `ind` y en `listInd` `substfcN` va sobre `liftfcN`. Las de la sustitución no las usa nadie todavía.
3. **Las guardas dan árboles:** `codT_of_hasWitN : hasWitN c → CodT c` y `codF_of_hasWitFN : hasWitFN c → CodF c`, por
   inducción fuerte en el número: el testigo es una lista cerrada por los constructores, y un hijo es menor que su padre
   (`memN_lt`). Es la mitad de la caracterización en ℕ que LEE el árbol; la otra, construir el testigo, es de GuardNeg.
4. **Términos**, por recursión mutua sobre `CodT`/`CodTs`: `prf_substtc_numeral` (`substtc k̄ s̄ c̄ = ⟨substtcN k s c⟩‾`,
   con cualquier sustituyendo) y `prf_liftc_numeral`, con sus listas. La variable, por tricotomía, con
   `prf_lt_numeralM` y las tres ecuaciones de `ArithPrf` (`prf_substtc_var_gt` y sus hermanas).
5. **Fórmulas**, por inducción sobre `CodF`: `prf_liftfc_numeral` y `prf_substfc_numeral`
   (`CodF f → CodT t → Prf (substfc v̄ t̄ f̄ = ⟨substfcN v t f⟩‾)`). Bajo `∀`/`∃` el sustituyendo pasa a `liftc 0 t̄`, que el
   punto 4 evalúa porque `t` es bueno: de ahí la hipótesis sobre `t`.
6. **Con las guardas de las líneas** (`hasWitFN`, `hasWitN`, las de `lineWFT`): `prf_substfc_guarda`,
   `prf_liftfc_guarda`, `prf_substtc_guarda` y `prf_liftc_guarda`. Es la forma que consumirá NegLineWF.
7. **Las dos congruencias de listas** que faltaban, `prf_congr_liftsc` y `prf_congr_substtsc3`, bajan a
   `Meta/NumCodeClosedPrf.lean`, junto a sus gemelas. Es el sitio y la firma (el nivel implícito) que pedía la nota de
   `Meta/CodeWitnessPrf.lean`, y la nota lo dice.

### 2 · Los controles

* **No es vacía:** `codF_codeNat`, el código de toda fórmula es bueno, y `prf_substfc_codeNat` aplica la evaluación al
  código de toda fórmula y de todo término. `codT_TC0`, `codT_TCS`, `codT_TNIL` y `codT_TCONS`: los códigos cerrados que
  incrustan `ind` y `listInd` son buenos.
* **La hipótesis puede fallar:** `not_hasWitFN_zero`.
* **Las dos guardas a la vez** (la lente de vacuidad, sobre la conjunción): `guardas_satisfacibles`, `hasWitFN ⌜⊥⌝` y
  `hasWitN ⌜v₀⌝`.
* **T08:** los 13 resultados del `#pureza` son PUROS (cierres de 83 a 786 constantes del proyecto). El control
  positivo, `ev_numeralM`, sale IMPURO.

### 3 · Lo medido

* **Los footprints:** `prf_liftc_numeral`, `prf_liftfc_numeral` y `codF_of_hasWitFN`, `[propext, Quot.sound]`;
  `prf_substtc_numeral`, `prf_substfc_numeral` y `prf_substfc_guarda`, con `Classical.choice` además. Lo traen
  `prf_substtc_func` y `prf_substtsc_cons`, de `ArithPrf`; no lo trae nada de esta etapa (sus `#print axioms`, medidos):
  `prf_substtc_var`, la tricotomía de esta etapa, sale sin él, y `prf_substTerm_arith`, la evaluación canónica, lo lleva
  igual. `check-footprints`: los 509 cuadran; [COBERTURA], 480 de 480.
* **Las líneas**, en la unidad de ADR‑147: §1, 17; §2, 57; §3, 75; §4, 10; §5, 68; §6, 93; §7, 12. En total, 332, y 15
  de las dos congruencias de `NumCodeClosedPrf`: 347. Los controles, 48; el módulo entero, 405. La ESTIMACIÓN de
  ADR‑146 §5 era 350–600.
* **La compilación:** al segundo intento. En el primero, el `∈` de dos lemas de listas resolvía al `In` OBJETO (la
  trampa de notación conocida), y se escribió `List.Mem`. `RosserNumEval` compila en 7 s.
* **El build**, el 2026-10-17: 134 jobs y 117 módulos, en 295 s, porque tocar `NumCodeClosedPrf` rehace todo lo que lo
  importa. Los 13 sondeos de control compilan, y los avisos son los 11 de la tabla de `check-warnings`: ninguno nuevo.
* **De paso:** `REFERENCE.md` decía «85 en `sondeos/`», una cifra de antes de ADR‑141. Hoy son 44, los que cuenta `[H]`.

### 4 · Las consecuencias

* **Lo siguiente, GuardNeg** (ADR‑146 §3, etapa 3): `¬hasWitN c → Prf ¬hasWit c̄`, y lo mismo para `hasWitF`. Pide la
  mitad de la caracterización en ℕ que falta (construir el testigo) y la hereditaria general. Su ESTIMACIÓN no cambia.
* **Lo que NumEval no cubre:** la basura. Sobre lo que no es un árbol `substfc` no está fijado, y NegLineWF no lo
  evalúa: una línea con la guarda falsa se refuta por GuardNeg.

**Véase también:** ADR‑146 §3 (la etapa), ADR‑147 (el orden), ADR‑150 (la capa de listas que usa) y ADR‑151 (el sondeo
de la guarda); T01 y T64 de la auditoría.

## ADR-153: 🔧 Rosser, etapa 3, GuardNeg: la guarda falsa se refuta en `Prf`, y queda decidida (`Meta/RosserGuardNeg.lean`)

**Fecha:** 2026-10-17 · **Estado:** ✅ hecho (este commit) · **Ámbito:** `Meta/RosserGuardNeg.lean` (nuevo), `Meta.lean`,
`check-footprints.bash` (seis filas), `REFERENCE.md` (84zd y la cifra de módulos), `doc/REFERENCE-Incompleteness.md` y
`CURRENT-STATUS-PROJECT.md` (las cifras), `TEOREMAS-E-HIPOTESIS.md` (el banner y la fila de Rosser), `NEXT-STEPS.md` y
`doc/AUDITORIA-SUELO-2026-10-12.md` (T01 y T64). Es el sexto paso del orden de ADR‑147, y el de más riesgo
(ADR‑146 §4.4).

### 1 · Qué se hizo

Para todo numeral, la mitad negativa de las dos guardas:

    ¬ hasWitN c  → Prf (¬ hasWit c̄)        prf_neg_hasWit
    ¬ hasWitFN c → Prf (¬ hasWitF c̄)       prf_neg_hasWitF

1. **La caracterización en ℕ, completa.** La mitad nueva construye el testigo de un código bueno juntando los de sus
   hijos (`hasWitN_of_codT`, `hasWitFN_of_codF`; para una lista de términos, `witTs_of_codTs`; las cláusulas son
   monótonas en los testigos). Con la mitad de ADR‑152: `hasWitN c ↔ CodT c` y `hasWitFN c ↔ CodF c`.
2. **Los refutadores, por la forma posicional.** La forma ecuacional de la guarda se fortalece a la posicional (ya lo
   hacía `Meta/CodeWitnessPrf.lean`), que expone la etiqueta y la longitud. Una forma con otra etiqueta o con otra
   longitud cae (`rej_cOk2`, `rej_cOk3`). La longitud se evalúa siempre (`prf_lenc_numeral`), y con ella caen el `0` y
   las etiquetas buenas con forma mala (`[0]‾`, `[1, s]‾`), que la etiqueta sola no tocaba. Con la etiqueta, un
   selector deja una sola de las ocho cláusulas de fórmula (`prf_B2_sel3`…`prf_B2_sel9`): `sondeos/RosserHasWitF.lean`
   tenía selectores para dos etiquetas, y aquí están todas.
3. **La dicotomía**, por inducción fuerte en el número: `codT_or_rejT : CodT c ∨ RejT c` y `codF_or_rejF`, donde
   `RejT c` dice que `Prf` saca `c̄` de toda lista testigo. Si la forma de `c` no es la de un código, cae por (2). Si lo
   es, la carga de su cláusula pone un hijo en la misma lista testigo, y el hijo cae por la hipótesis de inducción (los
   de término de `eq` y de `atom`, por la dicotomía de términos). Juntar las dicotomías de los argumentos es
   `list_or`, por la lista: nada usa lógica clásica.
4. **Los titulares:** `prf_neg_hasWit` y `prf_neg_hasWitF` (con la caracterización, `¬hasWitN c → ¬CodT c`), y la
   guarda DECIDIDA: `hasWit_decide : hasWitN c ∨ Prf ¬hasWit c̄` y `hasWitF_decide`.

### 2 · Los controles

* **La hipótesis se cumple:** `control_neg_hasWit_zero` y `control_neg_hasWitF_zero`, el `0`, por el teorema general.
* **Es exacta:** `control_exacta` y `control_exactaF`. Donde la guarda vale en ℕ, `Prf` no la refuta (la solidez en
  `MNV V₀`). Con GuardNeg: `Prf ¬hasWit c̄` si y sólo si `¬hasWitN c`.
* **T08:** los 12 resultados del `#pureza` son PUROS (cierres de 125 a 882 constantes del proyecto). Los dos controles
  exactos, IMPUROS, como se espera: son el control positivo.

### 3 · Lo medido

* **Compiló a la primera**, sin avisos: 48 s con `lake env lean`, 7,8 s en el build.
* **Los footprints:** los seis impresos, `[propext, Quot.sound]`, sin `Classical.choice`. `check-footprints`: los 515
  cuadran; [COBERTURA], 486 de 486.
* **Las líneas**, en la unidad de ADR‑147: §1 (la caracterización), 136; §2 (las formas en ℕ), 46; §3 (los
  refutadores), 199, de ellas 77 de los siete selectores; §4 (la dicotomía), 61; §5 (los titulares), 28. En total, 470.
  La caracterización, 136, frente a una ESTIMACIÓN de 60–150; lo demás, 334, frente a 350–550 (ADR‑146 §5). Los
  controles, 20; el módulo entero, 514.
* **El build**, el 2026-10-17: 135 jobs y 118 módulos. Los 13 sondeos de control compilan, y los avisos son los 11 de la
  tabla de `check-warnings`. `[A2]` baja de 37 a 22 por una coincidencia y no por un arreglo: 15 líneas históricas del
  cuerpo dicen la cifra de jobs de hoy (la del 2026-10-17, tras esta etapa), y con el próximo módulo vuelven.

### 4 · Las consecuencias

* **El riesgo de ADR‑146 §6.1 se cierra.** GuardNeg era la etapa de más riesgo y salió sin sorpresas. El `∃∃` y las ocho
  cláusulas se resolvieron con lo que ya había (la forma posicional y sus refutadores); la hereditaria general, con
  una dicotomía.
* **Lo siguiente, NegLineWF** (ADR‑146 §3, etapa 4): `¬lineWFT V K x → Prf ¬lineWF x̄`, por etiqueta. En las siete
  etiquetas de sustitución usa GuardNeg donde la guarda es falsa y NumEval donde es verdadera (`prf_substfc_guarda`).
* **Los dos sondeos de control de la guarda** (`RosserBasura` §1–§4 y `RosserHasWitF`) afirman hoy casos de
  `prf_neg_hasWit` y `prf_neg_hasWitF`. ADR‑146 §4.6 dejaba a `RosserBasura` sólo su §5. Sus pruebas van por otro
  camino (los refutadores de profundidad fija) y compilan: se quedan, y se decide con T66, al final, con lo demás que
  NegNum no use.

**Véase también:** ADR‑146 §3, §4.4 y §6.1 (la etapa y el riesgo), ADR‑147 (el orden), ADR‑151 (el sondeo de
`hasWitF`) y ADR‑152 (la mitad de la caracterización que lee el testigo); T01 y T64 de la auditoría.

## ADR-154: 🔧 Rosser, etapa 4, NegLineWF: la línea mala se refuta, y la buena formación de una línea queda decidida (`Meta/RosserNegLinea.lean`)

**Fecha:** 2026-10-17 · **Estado:** ✅ hecho (este commit) · **Ámbito:** `Meta/RosserNegLinea.lean` (nuevo), `Meta.lean`,
`check-footprints.bash` (seis filas), `REFERENCE.md` (84ze y la cifra de módulos), `doc/REFERENCE-Incompleteness.md` y
`CURRENT-STATUS-PROJECT.md` (las cifras), `TEOREMAS-E-HIPOTESIS.md` (el banner y la fila de Rosser), `NEXT-STEPS.md` y
`doc/AUDITORIA-SUELO-2026-10-12.md` (T01 y T64). Es el séptimo paso del orden de ADR‑147.

### 1 · Qué se hizo

Para el numeral de cualquier línea, con `Vax = codeNatList axioms`, el valor de `axiomsCodeT` por el ancla:

    lineWF_decide x : lineWFN Vax x ∨ Prf (¬ lineWF x̄)
    prf_neg_lineWF  : ¬ lineWFN Vax x → Prf (¬ lineWF x̄)

1. **Las 21 instancias de `ax_lineWF_*`** en una línea cualquiera `X`, en la dirección directa (`axL_p1`…`axL_listInd`):
   con la etiqueta `k`, `lineWF X` da la RHS de su regla. Las RHS se copiaron de `Minimal/Axioms.lean` con un guion
   (`(.var 0) ↦ X`, salvo dentro de `termCodeM`), y el núcleo las comprueba: cada una cierra por definición con la
   instancia del axioma (un lema genérico, `prf_lineWF_rhs`). `ind` y `listInd` piden más profundidad de recursión
   (`maxRecDepth`), por los códigos cerrados de sus términos.
2. **La evaluación sobre el numeral.** Las RHS usan accesores (`lenc`, `carc`, `nthc`), que sobre el numeral se evalúan
   (ADR‑150); las reconstrucciones, con los constructores de código (`evImpl`…), la sustitución y el lift (NumEval,
   ADR‑152: `evSubst`, `evLift`), y los códigos cerrados de `ind`/`listInd` (`evTC`). Para `thy`, el ancla:
   `axiomsCodeT = listFormCodeM axioms` (`prf_ancla`), que es el numeral de `codeNatList axioms` por la lista
   (`prf_listFormCodeM_numeral`, sin desplegar nada); con ello, `prf_not_In_axiomsCodeT`.
3. **Una rama de la inversión cae** (`Rama x k`): por la longitud, que se evalúa siempre; por la etiqueta, si se puede
   leer; o por su RHS. La de la etiqueta propia se DECIDE (`refT_of`): las guardas, con GuardNeg (ADR‑153); la
   conclusión, comparada en ℕ con su reconstrucción evaluada; `thy`, por la pertenencia en ℕ, decidible sin lógica
   clásica.
4. **Las 21 reglas** (`refT_p1`…`refT_listInd`), una a una, y el ensamblaje por `ax_lineWF_inv` (`prf_lineWF_inv`):
   `lineWF_decide` y `prf_neg_lineWF`.

### 2 · Los controles

* **La hipótesis se cumple:** `control_neg_lineWF_zero`, el `0` no es una línea, por el teorema general.
* **Es exacta:** `control_exacta`, donde la línea es buena en ℕ, `Prf` no la refuta (la solidez en `MNV V₀`, con
  `V₀_eq_codigo`). Con NegLineWF: `Prf ¬lineWF x̄` si y sólo si `¬lineWFN Vax x`.
* **T08:** los 6 resultados del `#pureza` son PUROS (cierres de 634 a 1 281 constantes del proyecto); `control_exacta`,
  IMPURO, como se espera.

### 3 · Lo medido

* **Compiló al segundo intento**: 9 s con `lake env lean`, 8,6 s en el build. En el primero, `k ≤ 20 → …` se leía mal (el
  `≤` objeto, con su precedencia, se tragaba la flecha) y se escribió `k < 21`; y el control exacto reescribía `V₀`
  antes que el numeral. Las 21 instancias y las 21 reglas compilaron a la primera.
* **Los footprints:** los seis impresos llevan `Classical.choice`, y no lo trae nada de esta etapa (medido): llega por
  `prf_ancla` (en `thy`) y por las ecuaciones de la sustitución de `ArithPrf` (en NumEval). Las reglas
  proposicionales, sin él (`refT_p1`, `refT_mp`, `[propext, Quot.sound]`). `check-footprints`: los 521 cuadran;
  [COBERTURA], 492 de 492.
* **Las líneas**, en la unidad de ADR‑147: §1, 12; §2 (las 21 instancias), 95; §3 (la evaluación), 65; §4 (las ramas),
  30; §5 (las 21 reglas), 108; §6 (el ensamblaje), 76. En total, 386; los controles, 13; el módulo entero, 423. La
  ESTIMACIÓN de ADR‑146 §5 era 450–650, con «las 8 proyecciones que faltan» (unas 96): no hicieron falta, porque las
  instancias de los axiomas dan la RHS entera.
* **El build**, el 2026-10-17: 136 jobs y 119 módulos. Los 13 sondeos de control compilan, y los avisos son los 11 de la
  tabla de `check-warnings`.

### 4 · Las consecuencias

* **Lo siguiente, NegNum** (ADR‑146 §3, etapa 5): `¬ProofN m y → Prf ¬PfF m̄ ȳ`. La cadena se decide línea a línea con
  `lineWF_decide`, y faltan las premisas (`premsOf`, `allIn`) sobre numerales y la «primera línea mala».
* **La línea `q1` basura** de T64 queda cubierta: toda línea mala de cualquiera de las 21 reglas se refuta. De T64 queda
  el `EV_TOK` de la etapa 7.

**Véase también:** ADR‑146 §3 (la etapa), ADR‑147 (el orden), ADR‑152 (NumEval) y ADR‑153 (GuardNeg); T01 y T64 de la
auditoría.

## ADR-155: 🧹 Dos arreglos pendientes: el docstring de `consistencia` dice que la consistencia es relativa a Lean (ADR‑138), y la pertenencia en ℕ es decidible sin lógica clásica (`decMemN`)

**Fecha:** 2026-10-17 · **Estado:** ✅ hecho (este commit) · **Ámbito:** `Meta/Consistencia.lean` (el docstring de
`consistencia`), `Meta/RosserNumerales.lean` (la instancia `decMemN` y el `#print axioms` de `prf_In_decide`),
`Meta/RosserNegLinea.lean` (pierde su copia), `check-footprints.bash` (una fila) y `NEXT-STEPS.md`. Los pidió el
propietario el 2026-10-17.

### 1 · El docstring de `consistencia`

ADR‑138 fijó que la consistencia que da `consistencia` es RELATIVA a Lean (PRA ⊢ Con(Lean) → Con(T_Prf)), y lo dijo en
los banners, en TEOREMAS §4, en AXIOMS §0.2 y en PLAN‑LIBRO. El docstring del propio teorema, en
`Meta/Consistencia.lean`, se quedó sin la precisión. Ahora la tiene, con la razón de que no puede ser absoluta
(`T_Prf` contiene a PA, y Gödel II) y la remisión a TEOREMAS §4.

### 2 · `decMemN`: la pertenencia en ℕ, decidible

ADR‑154 midió que `prf_In_decide` (`Meta/RosserNumerales.lean`, el control de ADR‑150) dependía de `Classical.choice`:
`by_cases` sobre `memN` no encuentra una instancia de `Decidable` (`memN` no es reducible) y cae en la clásica. La
instancia explícita, `decMemN` (la de `List.Mem` sobre `Nat`, `List.instDecidableMemOfLawfulBEq`), baja de
`Meta/RosserNegLinea.lean`, donde la escribió ADR‑154, a `Meta/RosserNumerales.lean`, aguas arriba. `prf_In_decide`
queda en `[propext, Quot.sound]`, medido; un `#print axioms` y su fila en `check-footprints` lo vigilan.

### 3 · Lo medido

* El build, el 2026-10-17: 136 jobs y 119 módulos, sin cambios. `check-footprints`: los 522 cuadran; [COBERTURA], 493
  de 493. Los 13 sondeos de control compilan, y los avisos son los 11 de la tabla de `check-warnings`.

**Véase también:** ADR‑138 (la consistencia relativa), ADR‑150 (`prf_In_decide`) y ADR‑154 (la medición).

## ADR-156: 🔧 Rosser, etapa 5, NegNum: el predicado de prueba de T, decidido sobre numerales, y NegNum′ con W1(ax) (`Meta/RosserNegNum.lean`)

**Fecha:** 2026-10-17 · **Estado:** ✅ hecho (este commit) · **Ámbito:** `Meta/RosserNegNum.lean` (nuevo), `Meta.lean`,
`check-footprints.bash` (cinco filas), `REFERENCE.md` (84zf y la cifra de módulos), `doc/REFERENCE-Incompleteness.md`
y `CURRENT-STATUS-PROJECT.md` (las cifras), `TEOREMAS-E-HIPOTESIS.md` (el banner y la fila de Rosser), `NEXT-STEPS.md` y
`doc/AUDITORIA-SUELO-2026-10-12.md` (T01). Es el octavo paso del orden de ADR‑147, y el último antes de Rosser.

### 1 · Qué se hizo

Con `PfF y x = chainOk nil y ∧ In x (runFn nil y)` (ADR‑149) y su espejo en ℕ, `ProofN` (ADR‑148):

    proofN_decide m y : ProofN m y ∨ Prf (¬ PfF m̄ ȳ)
    negNum            : ¬ ProofN m y → Prf (¬ PfF m̄ ȳ)
    negNum'           : ¬ Prf (dec y) → ∀ m, Prf (¬ PfF m̄ ȳ)

1. **Las premisas.** Sólo `mp` y `gen` tienen premisas: en las otras 19 reglas `premsOfN` es `0`. Su `premsOf` sobre el
   numeral lo dan `prf_premsOf_mp`/`prf_premsOf_gen` (`Meta/PremsOfTagPrf.lean`, ya en el build) con la cola del
   numeral evaluada (`prf_premsOf_mp_num`, `prf_premsOf_gen_num`). Una premisa que falta en el acumulador refuta la
   línea (`prf_neg_lineOk_prem`); la inclusión se decide en ℕ sin lógica clásica (`allInN_dec`, con `decMemN`).
2. **La cadena, decidida línea a línea** (`chainOk_decide`, por la lista): la línea mala cae por NegLineWF
   (`lineWF_decide`, ADR‑154); la premisa que falta, por (1); y la buena pasa a la cola con el acumulador evaluado
   (`prf_concat_numeral`, ADR‑150). Así queda decidida la «primera línea mala» de ADR‑146 §3, sin buscarla en ℕ.
3. **NegNum:** si la cadena es buena, la conclusión que falta se refuta con `prf_not_In_runFn` (ADR‑150; las líneas de
   una cadena buena no son `0`, `lines_ne_zero`).
4. **NegNum′, con W1(ax)** (ADR‑148): si `dec y` no es teorema, `ProofN m y` no vale para ningún `m` (`w1Ax`), y `Prf`
   refuta cada candidata (`negNum'`); sobre el código de una fórmula, `negNum_formula`, y con `formCode φ`, la forma de
   `posNum`, `negNum_formCode`. Es la mitad negativa que la sentencia de Rosser necesita.

### 2 · Los controles (los de ADR‑146 §4)

* **La hipótesis puede valer:** `control_negNum_vacia`, la cadena vacía no prueba nada (`not_proofN_zero`).
* **Y puede fallar:** `control_falla`, la prueba de un axioma ES una prueba (`proofN_axioma`), y `Prf` no la refuta.
* **Es exacta:** `control_exacta`, donde `ProofN` vale, `Prf` no refuta `PfF` (la solidez en `MNV V₀`).
* **T08:** los 7 resultados del `#pureza` son PUROS (cierres de 1 353 a 1 488 constantes del proyecto);
  `control_exacta` y `control_falla`, IMPUROS, como se espera.

### 3 · Lo medido

* **Compiló a la primera**, con dos avisos de argumentos de `simp` sobrantes en `control_exacta`, quitados: 14 s con
  `lake env lean`, 10 s en el build.
* **Los footprints:** `prf_neg_lineOk_prem`, `[propext, Quot.sound]`; los titulares, con `Classical.choice`, que llega
  por `lineWF_decide` (de `prf_ancla` y de `ArithPrf`, ADR‑154), no de esta etapa. `negNum'` no lleva `#print axioms`:
  `[COBERTURA]` corta los nombres en la prima. `check-footprints`: los 527 cuadran; [COBERTURA], 498 de 498.
* **Las líneas**, en la unidad de ADR‑147: §1, 24; §2 (las premisas), 69; §3 (la cadena), 29; §4 (NegNum), 25. En
  total, 147; los controles, 16; el módulo entero, 188. La ESTIMACIÓN de ADR‑146 §5 era 150–250.
* **El build**, el 2026-10-17: 137 jobs y 120 módulos. Los 13 sondeos de control compilan, y los avisos son los 11 de la
  tabla de `check-warnings`.

### 4 · Las consecuencias

* **Lo siguiente, la etapa 7: Rosser por la reducción** (ADR‑144/145): el caso `z ≤ n̄`, `Pf_E` y su transporte, la
  sentencia R con `IsSentence R`, y el argumento, con `posNum` y `negNum'`. `ExtensionPorReduccion` pasa a
  `Meta/Rosser.lean` (ADR‑146 §4.6).
* **NegNum queda decidido**, no sólo refutado: `proofN_decide` es constructivo salvo lo que hereda de las ecuaciones de la
  sustitución y del ancla.

**Véase también:** ADR‑146 §3 y §4 (la etapa y sus controles), ADR‑147 (el orden), ADR‑148 (W1(ax)), ADR‑149 (PosNum)
y ADR‑154 (NegLineWF); T01 de la auditoría.

## ADR-157: 🏁 Rosser, etapa 7: ROSSER por la reducción — `rosser_ext` para toda extensión finita T+E consistente, y `rosser` para T sin hipótesis (`Meta/Rosser.lean`); T08 lo acepta

**Fecha:** 2026-10-18 · **Estado:** ✅ hecho (este commit) · **Ámbito:** `Meta/Rosser.lean` (nuevo),
`Meta/PurezaComando.lean` (nuevo: el recorrido y `#pureza`, sacados de `Meta/PurezaTitulares.lean`),
`Meta/PurezaTitulares.lean` (la lista: `rosser_ext` en `PUROS`, `rosser` en `IMPUROS`), `Meta/RosserW1.lean`,
`Meta/RosserPosNum.lean` y `Meta/RosserNumerales.lean` (el import), `Meta.lean`, `check-footprints.bash` (ocho filas),
`check-doc-sync.bash` (`T_UNIVERSO`, dos nombres), `check-sorry.bash` (`R` en `EV_TOK`), `sondeos/InduccionTitulares.lean` (`#induccion`, `#modelo` y tres
`#camino` de los dos titulares), `sondeos/InventarioRosser.lean` (el `open`), `sondeos/ExtensionPorReduccion.lean`
(una nota), `TEOREMAS-E-HIPOTESIS.md`, `AXIOMS.md` §0.3, `REFERENCE.md`, `doc/REFERENCE-Incompleteness.md`,
`CURRENT-STATUS-PROJECT.md`, `NEXT-STEPS.md`, `sondeos/README.md`, `doc/AUDITORIA-SUELO-2026-10-12.md` (T01, T08, T64),
`doc/registro/2026-10-18-rosser/` y su índice. Es el último paso del orden de ADR‑147, y los pasos 2–4 de ADR‑145 §2.

### 1 · Qué se hizo

    rosser_red E         : ¬ PrfH E ⊥ → ¬ PrfH E (R E) ∧ ¬ PrfH E ¬(R E)          -- para toda lista E
    rosser_ext E hE hcon : lo mismo, con «E son sentencias» (el enunciado de ADR‑145)
    rosser               : ¬ Prf R ∧ ¬ Prf ¬R, con R = R []                        -- con `consistencia`

1. **La reducción** (§1 y §2 del módulo, promovidos de `sondeos/ExtensionPorReduccion.lean`): `PrfH E φ ↔ Prf (impChain
   E φ)` y `formCode (impChain E φ) = impChainC E (formCode φ)`. El predicado de prueba de T+E se DEFINE con el de T,
   `PfE E y x := PfF y (impChainC E x)`, y PosNum y NegNum de T+E (`posNumE`, `negNumE`) son `posNum` y
   `negNum_formCode` sobre `impChain E φ`, con un `rw`.
2. **La sentencia** (§3): ρ_E(x) := ∀y (Pf_E(y, x) → ∃z (z < y ∧ Pf_E(z, ¬x))), con ¬x el término `implc x botc`, y
   `R E`, su punto fijo por `prf_diagonal` (ADR‑121). `prf_R_fix` la da ya instanciada en ⌜R⌝ = `numeral (codeNat (R
   E))`, y `R_isSentence` dice que es una sentencia. ADR‑144 §3 escribía `z ≤ y`; con `<`, la forma de Rosser, bastan
   la tricotomía (`prf_lt_trichotomy`) y el ∀ acotado del árbol (`prf_bdAll_numeral`). Los dos códigos de R —el de
   `formCode`, que dan `posNum` y `negNum`, y el numeral del punto fijo— se igualan en T con `prf_formCode_numeral`, y
   la igualdad pasa por `impChainC` (`prf_PfE_congr`).
3. **El argumento** (§4), con T+E consistente:
   - (a) `rosser_no_R`: una prueba m̄ de R en T+E (PosNum) y ρ en m̄ dan ∃z < m̄ Pf_E(z, ⌜¬R⌝). T+E no prueba ¬R, así
     que NegNum refuta cada z; el ∀ acotado lo junta, y T+E sería inconsistente (`prfH_bot_of`).
   - (b) `rosser_no_negR`: una prueba m̄ de ¬R en T+E. T+E no prueba R, así que NegNum refuta cada candidata a prueba
     de R; por la tricotomía de y y m̄, T prueba el cuerpo de ρ(⌜R⌝) (`prf_rhoBody_of`: si y < m̄ o y = m̄, por NegNum;
     si m̄ < y, con m̄ de testigo), luego R, y T+E sería inconsistente.
4. **Los controles** (§6; CRI‑02 y ADR‑144 §3): la hipótesis puede FALLAR (`inconsistente_bottom`), y entonces la
   conclusión falla (`control_bottom : PrfH [⊥] (R [⊥])`); y las dos hipótesis de `rosser_ext` pueden VALER a la vez
   en una extensión NO sólida, T+¬Con: ¬Con es una sentencia (`negCon_isSentence`) y T+¬Con es consistente
   (`consistente_neg_con`, por `goedel_II`), y Rosser vale por el titular (`control_neg_con`, con `rosser_ext`).

### 2 · `hE` no la usa la prueba (MEDIDO)

El `gen` de `PrfH` sube el contexto (`PrfH (Γ.map (liftFormula 0)) A → PrfH Γ (∀A)`): el teorema de deducción, y con él
la reducción, valen para TODA lista E, y la prueba de Rosser no necesita que E sean sentencias. `rosser_red` es el
teorema sin `hE`, y `rosser_ext` lo llama con la hipótesis nombrada `_hE`. Con `hE`, el linter avisa (MEDIDO en un
fichero aparte: «Variable name `hE` is not explicitly referenced»), y `check-warnings` no admite un aviso sin declarar. Lo que `hE` da es la LECTURA: con E de sentencias, `PrfH E` es la teoría T+E
(ADR‑144 §7). Con E abierta, por lectura, sus variables libres hacen de parámetros: sobre sentencias, `PrfH E` es
T + ∃x⃗ ⋀E (por la deducción y `gen`), no T más el cierre universal: `PrfH [#0 = 0]` es consistente, y T + ∀x (x = 0)
no. Se queda en el enunciado, que es el que decidió ADR‑145; si se prefiere el más fuerte como titular, es cambiar
el nombre de una fila. ✏️ *(el mismo día, [ADR‑158](#adr-158))*: decidido así; `rosser_red`, la forma más fuerte.

### 3 · T08: Rosser es de la clase (i), y entra en `PUROS`

* **El ciclo de ADR‑148 §3**, resuelto como allí se anunciaba: el recorrido y el comando `#pureza` pasan, tal cual, a
  `Meta/PurezaComando.lean`, con el control `mutanteLocal` (el espacio de nombres pasa a
  `ROBINSON_PlusPlus.Meta.PurezaComando`); `Meta/PurezaTitulares.lean` queda con la lista, `PUROS` e `IMPUROS`, y
  `#pureza_titulares`, e importa `Meta/Rosser.lean`. Los tres módulos de Rosser que importaban `PurezaTitulares`
  importan `PurezaComando`.
* **`#pureza_titulares`, en el build:** 9 PUROS —los 8 de antes y `rosser_ext`, con 1 914 constantes del proyecto en su
  cierre— y 3 controles positivos, IMPUROS: `goedel_I`, `tarski` y `rosser`.
* **El `#pureza` del módulo:** 8 PUROS (`prfH_iff_prf_impChain`, `formCode_impChain`, `posNumE`, `negNumE`,
  `R_isSentence`, `rosser_red`, `rosser_ext`, `control_bottom`) y 2 IMPUROS: `rosser`, por `consistencia`, y
  `control_neg_con`, por `goedel_II`.
* **Visto fallar en los dos sentidos**, con tres mutantes (`doc/registro/2026-10-18-rosser/mutantes-t08.md`): `rosser`
  como puro FALLA («nombra la semántica: rosser ⟶ consistencia ⟶ consistentH_de»); `rosser_ext` como control
  positivo FALLA («el criterio está CIEGO»); y el enunciado de `rosser_ext` con una prueba que NOMBRA `prf_sound`, la
  raíz de la ruta de `sondeos/RosserReflexion.lean`, como puro FALLA («mutanteReflexion ⟶ prf_sound»). El tercero
  sólo comprueba que T08 ve la mención de `prf_sound`, no que la ruta de la reflexión se recorra. Su primera versión
  no compilaba y salía PURA: un mutante que no compila no mide nada.
* **`#modelo`** (`sondeos/InduccionTitulares.lean`): `rosser_ext`, clase (i), sin ninguna constante de la semántica en
  el cierre; `rosser`, clase (ii): 90, y ninguna sin pasar por `consistencia`.

### 4 · Lo que usa de las reglas (MEDIDO, `#induccion` y `#camino`)

* **`ind`, sí,** por el ∀ acotado: `prfH_bot_of ⟶ prf_bdAll_numeral ⟶ prf_lt_succ_split ⟶ … ⟶ prf_zero_or_succ ⟶
  prf_nat_induction` (10 aristas de valor). Es el Q3 de Robinson que también usa D1 (ADR‑134).
* **`listInd`, sí,** por NegNum: `negNumE ⟶ … ⟶ chainOk_decide ⟶ … ⟶ prf_list_induction` (22 aristas).
* **`p3`, sólo al DECODIFICAR:** `negNum' ⟶ w1Ax ⟶ cadena_buena ⟶ linea_buena ⟶ linea_p3` (11 aristas). W1(ax) convierte
  una prueba en ℕ con el código de los 142 en una derivación de `Prf`, con los `p3` de sus líneas, en el caso que NegNum′
  descarta; `goedel_I_neg` decodifica igual las líneas que el verificador acepta en el modelo. `AXIOMS.md` §0.3 decía
  «ningún titular construye un paso clásico salvo `goedel_I_neg`»; ahora dice: salvo `goedel_I_neg`, `rosser_ext` y
  `rosser`, los tres al decodificar.

### 5 · Lo medido

* **Compiló con dos arreglos:** una ambigüedad (`liftTerm_numeralM` está en `Minimal.Axioms` y en `PremsOfDotPrf`) y la
  conjunción de los enunciados: entre proposiciones, `¬ P ∧ ¬ Q` se resolvía al `∧` de FOL (`Formula.and`), y va con
  `And`. 10 s con `lake env lean`, 9 s en el build.
* **Los footprints:** `prfH_iff_prf_impChain`, `[propext]`; `formCode_impChain`, ninguno; `R_isSentence`, `[propext,
  Quot.sound]`; `posNumE`, `negNumE` y los tres titulares, `[propext, Classical.choice, Quot.sound]`, que heredan de
  PosNum y NegNum. `check-footprints`: los 535 cuadran.
* **Las líneas**, en la unidad de ADR‑147 (las no vacías tras `strip-lean.awk`, `grep -cv '^[[:space:]]*$'`): §1, 15;
  §2, 44; §3, 86; §4, 75; §5, 10; §6 con los `#print axioms` y el `#pureza`, 37 (los controles, 23); la cabecera, 10;
  el módulo, 277. Rosser sin los controles (§1–§5), 230; la ESTIMACIÓN de ADR‑144 §4 era 200–400. `PurezaComando` y
  `PurezaTitulares`, 101 y 25, frente a 116 del módulo único. ✏️ La primera versión de este ADR contaba con `grep -c .`,
  que cuenta también las líneas de espacios que `strip-lean.awk` deja donde había un docstring (lo vio la revisión
  adversarial); con esa cuenta daba 312, 263, 112 y 30. Fe de erratas de ADR‑156 §3: el módulo de NegNum tiene hoy
  187 líneas, no 188 (INFERIDO: la diferencia es el `#print axioms` de `negNum'`, quitado después de medir).
* **El build**, el 2026-10-18: 139 jobs y 122 módulos (Meta 117). Los avisos son los 11 de la tabla de `check-warnings`.

### 6 · Las consecuencias

* **🏁 Rosser, hecho.** Con Gödel I entero, Gödel II y Tarski, el tercero de la línea de llegada de ADR‑140 (los 18 de
  `T_UNIVERSO`, Rosser y Löb): queda Löb (T70). ✏️ *(el mismo día, [ADR‑159](#adr-159))*: hecho.
* **`T_UNIVERSO` pasa de 18 a 20 titulares:** `rosser_ext`, de la clase (i), y `rosser`, de la (ii). ✏️ *(el mismo
  día, [ADR‑158](#adr-158))*: `rosser`, titular, decidido.
* **T64, cerrado,** con lo último que pedía: `R` en `EV_TOK` (`check-sorry.bash`). `R E` es `selfAppN` de la plantilla
  y lleva el numeral de su código, así que una orden que la evaluara no acabaría. Visto fallar: con la línea de `R` en
  el autotest y sin el token, el control daba «SIN MEDIR»; con el token, verde. Los señuelos `rhoE` y
  `Rosser.prf_R_fix` no casan. El token cuenta por BYTES: `R₀` casaría (el lado seguro) y `«R»` se escaparía.
* **La Etapa 0 y el sondeo de la reducción** (`RosserBasura`, `RosserHasWitF`, `RosserReflexion`,
  `ExtensionPorReduccion`) se quedan como están: qué se borra, se reduce o se porta es T66, al final (ADR‑147), midiendo
  qué usó NegNum.

**Véase también:** ADR‑121 (el lema diagonal), ADR‑137, ADR‑143 (T08), ADR‑144 y ADR‑145 (la reducción), ADR‑146 y
ADR‑147 (el plan), ADR‑148 (W1(ax) y el ciclo), ADR‑149 (PosNum) y ADR‑156 (NegNum); T01, T08, T62 y T66 de la
auditoría.

## ADR-158: 🧭 Las decisiones del propietario sobre ADR‑157: `rosser_ext` con `_hE`, el titular; `rosser_red`, la forma más fuerte; `rosser`, titular; lo siguiente, Löb

**Fecha:** 2026-10-18 · **Estado:** ✅ decidido (este commit) · **Ámbito:** el estado de ADR‑157 (§2 y §6). Ningún
cambio de código ni de tablas: ADR‑157 ya lo dejó así.

### 1 · Las decisiones

1. **`rosser_ext`, con la hipótesis `_hE` que la prueba no usa, sigue de titular** (en `PUROS` y en `T_UNIVERSO`), y
   `rosser_red` queda como la forma más fuerte, para toda lista E. Era la recomendación de ADR‑157 §2: `_hE` es lo que
   hace de `PrfH E` la teoría T+E, y el enunciado de ADR‑145 habla de teorías.
2. **`rosser`, Rosser para T sin hipótesis, es titular**, de la clase (ii), al lado de `goedel_I` y `goedel_II`.
3. **Lo siguiente, Löb** (T70): ADR‑159.

**Véase también:** ADR‑145, ADR‑157 y ADR‑159.

## ADR-159: 🏁 LÖB: `lob : Prf (Prov⌜φ⌝ ⇒ φ) → Prf φ` y `lob_iff`, por el punto fijo de `Prov(#0) ⇒ φ` y D1–D3 (`Meta/Lob.lean`); Gödel II, de corolario; la línea de llegada de RPP, completa en sus teoremas

**Fecha:** 2026-10-18 · **Estado:** ✅ hecho (este commit) · **Ámbito:** `Meta/Lob.lean` (nuevo),
`Meta/PurezaTitulares.lean` (`lob` en `PUROS`), `Meta.lean`, `check-footprints.bash` (cuatro filas),
`check-doc-sync.bash` (`T_UNIVERSO`: `lob`), `check-sorry.bash` (`lobSent` en `EV_TOK`),
`sondeos/InduccionTitulares.lean` (`#induccion` y `#modelo` de `lob`), `TEOREMAS-E-HIPOTESIS.md`, `AXIOMS.md` §0.3,
`REFERENCE.md`, `doc/REFERENCE-Incompleteness.md`, `CURRENT-STATUS-PROJECT.md`, `NEXT-STEPS.md`, `sondeos/README.md`,
`doc/AUDITORIA-SUELO-2026-10-12.md` (T70), `doc/registro/2026-10-18-lob/` y su índice. Es T70, el último teorema de
la línea de llegada de ADR‑140.

### 1 · Qué se hizo

    lob φ     : Prf (Prov⌜φ⌝ ⇒ φ) → Prf φ
    lob_iff φ : Prf (Prov⌜φ⌝ ⇒ φ) ↔ Prf φ

con Prov⌜ψ⌝ = `provCodeC' ψ`, el de D1–D3.

1. **La sentencia de Löb** de φ, `lobSent φ`, es el punto fijo (`prf_diagonal`, ADR‑121) de `lobPred φ := Prov(#0) ⇒
   ↑φ`, con φ subida un nivel (`liftFormula 0`): al sustituir `#0` por el código, φ vuelve intacta
   (`FOL.substFormula_liftFormula`), así que no tiene que ser una sentencia. `prf_lob_fix : L ⇔ (Prov⌜L⌝ ⇒ φ)`: el punto
   fijo da el código en forma de numeral, y `prf_provCode_transfer` lo pasa al de `formCode` (con
   `prf_imp_congr_left_iff`).
2. **El argumento de siempre** (§2): de L ⇒ (Prov⌜L⌝ ⇒ φ), por D1 y D2, Prov⌜L⌝ ⇒ Prov⌜Prov⌜L⌝ ⇒ φ⌝; por D2 y D3,
   Prov⌜L⌝ ⇒ Prov⌜φ⌝; con la hipótesis, Prov⌜L⌝ ⇒ φ; por la vuelta del punto fijo, L; por D1, Prov⌜L⌝; y φ. Es la
   estructura de `prf_con_imp_godel`, con φ en lugar de ⊥.
3. **`lob_iff`**: la otra dirección es la fácil (P1). T demuestra la reflexión exactamente para sus teoremas.

### 2 · Los controles

* **El corolario de T70** (`goedel_second_de_lob`): Gödel II sale de Löb con φ = ⊥ en una línea, porque
  `consistencyFormula'` ES Prov⌜⊥⌝ ⇒ ⊥. Es el enunciado de `goedel_second_prf`, con `hcon : ConsistentH`, por otro
  camino; los dos son de la clase (i).
* **La hipótesis puede fallar:** `control_reflexion_bot : ¬ Prf (Prov⌜⊥⌝ ⇒ ⊥)` (con `consistencia`: es Gödel II) y
  `control_reflexion_godel : ¬ Prf (Prov⌜G⌝ ⇒ G)` (con `goedel_I`).
* **Y puede valer:** `control_reflexion_teorema`, para ⊥ ⇒ ⊥, por la dirección fácil de `lob_iff`.
* **T08:** el `#pureza` del módulo da 5 PUROS (`prf_lob_fix`, `lob`, `lob_iff`, `goedel_second_de_lob`,
  `control_reflexion_teorema`) y 2 IMPUROS (los dos controles que fallan). `#pureza_titulares`: 10 PUROS, con `lob`
  (3 270 constantes del proyecto en su cierre), y los 3 controles positivos de ADR‑157. Visto fallar con tres mutantes
  (`doc/registro/2026-10-18-lob/mutantes-t08.md`): `control_reflexion_bot` como puro, `lob` como control positivo, y el
  enunciado de `lob` con una prueba que nombra `prf_sound`, como puro. La salida tiene los tres errores de T08 y
  ninguno de elaboración.
* **`#modelo`** (`sondeos/InduccionTitulares.lean`): `lob`, clase (i), sin ninguna constante de la semántica en su
  cierre (4 935 constantes, con las de Lean).
* **`#induccion`:** `ind`, sí (por D1); `listInd`, sí (por D2); `p3`, no. Lo mismo que `goedel_second_prf`.
* **`EV_TOK`:** `lobSent` lleva el numeral de su propio código, como `R`; entra en el censo de `check-sorry.bash`, con su
  autotest visto fallar (con la línea en el autotest y sin el token, «SIN MEDIR»).

### 3 · Lo medido

* **Compiló a la primera:** 40 s con `lake env lean` (casi todo, la carga de las importaciones), 12 s en el build.
* **Los footprints:** los cuatro (`prf_lob_fix`, `lob`, `lob_iff`, `goedel_second_de_lob`), `[propext,
  Classical.choice, Quot.sound]`, los de D1–D3 y el punto fijo. `check-footprints`: los 539 cuadran.
* **Las líneas**, en la unidad de ADR‑147: §1 (la sentencia y el punto fijo), 19; §2 (Löb), 14; §3 con los
  `#print axioms` y el `#pureza`, 17 (los controles, 9); la cabecera, 10; el módulo, 60. Löb sin los controles, 33; la
  ESTIMACIÓN de T70 era 50–120.
* **El build**, el 2026-10-18: 140 jobs y 123 módulos (Meta 118).
* **`[A2]`**, 37 avisos, como antes de ADR‑157 (allí, 34): tres líneas históricas de `doc/REFERENCE-Incompleteness.md`
  dicen «139 jobs», la cifra de entonces (ADR‑157), y vuelven a saltar con 140. No son de hoy.

### 4 · Las consecuencias

* **🏁🏁 La línea de llegada de RPP (ADR‑140), completa en sus teoremas:** los 18 titulares de `T_UNIVERSO`, Rosser
  (ADR‑157) y Löb. `T_UNIVERSO` tiene 21. Lo que queda es de la auditoría: T66 (los sondeos de Rosser), T04, T04b,
  T07 y T15, y los corolarios baratos de T78.
* **Löb formalizado** (Prov⌜Prov⌜φ⌝ ⇒ φ⌝ ⇒ Prov⌜φ⌝) no está: T70 no lo pedía.

**Véase también:** ADR‑121 (el lema diagonal), ADR‑140 (la línea de llegada), ADR‑143 (T08), ADR‑157 (Rosser) y
ADR‑158; T70 y T78 de la auditoría.

## ADR-160: 🧹 T66: el subárbol sin consumidor, fuera del build —`ChainNegPrf`, `VerifierSound`, `OmegaReflect`, `ChainDecode` y `CodeDecode`—, medido con el cono de los 21 titulares; y los sondeos de Rosser, ordenados

**Fecha:** 2026-10-18 · **Estado:** ✅ hecho (este commit) · **Ámbito:** los cinco módulos (borrados; en la etiqueta
`archivo/t66-2026-10-18`), `Meta.lean`, `check-footprints.bash` (26 filas fuera), `check-warnings.bash` (la fila de
`ChainNegPrf`), `sondeos/ConoTitulares.lean` (los 21 titulares; la fecha y la carpeta, datos; el control (2)),
`sondeos/IteSimboloNucleo.lean` y `sondeos/OmegaConsistentRefutable.lean` (copian lo que usaban),
`sondeos/RosserBasura.lean` (§5), `sondeos/CONTROLES.txt` (dos pasan a REGISTRO), `sondeos/DespachadorCoste.lean`
(archivado), `sondeos/ExtensionPorReduccion.lean` y `sondeos/RosserHasWitF.lean` (notas), `sondeos/README.md`, los
comentarios de `Meta/CodeDistinct.lean`, `Meta/LineWFCases.lean` y `Meta/RosserNegLinea.lean`, DECISIONS (la
Verificación de M‑8 y ADR‑146 §3 y §4.6), `REFERENCE.md`, `TEOREMAS-E-HIPOTESIS.md`, `doc/REFERENCE-Incompleteness.md`,
`CURRENT-STATUS-PROJECT.md`, `NEXT-STEPS.md`, `doc/AUDITORIA-SUELO-2026-10-12.md` (T66, T76),
`doc/registro/2026-10-18-cono/` y su índice. Es T66 de la auditoría, que ADR‑147 dejó «al final, midiendo con el cono
qué usó NegNum».

### 1 · La medida (`sondeos/ConoTitulares.lean`, con los 21 titulares)

* **El cono del núcleo** de los 21 titulares (los 18, `rosser_ext`, `rosser` y `lob`): 4 416 constantes del proyecto,
  3 209 declaraciones y 31 103 líneas. Los controles del sondeo pasan.
* **Sin nada en el cono, 23 módulos importados:** los 21 del 2026‑10‑16, y `PurezaComando` y `PurezaTitulares`, de
  elaboración. Entre ellos, el subárbol de T66: `ChainNegPrf` (1 617 líneas, 109 declaraciones), `VerifierSound` (154,
  6), `OmegaReflect` (314, 18), `ChainDecode` (422, 30) y `CodeDecode` (446, 18). En total, 2 953 líneas y 181
  declaraciones, ninguna en el cono.
* **Rosser no heredó nada de `ChainNegPrf`.** ADR‑146 §4.6 preveía usar sus `prf_lineTag_cons` (retirado),
  `prf_boundedPremsIn_of_chainOk` (retirado) y las 21 `prf_lenc_<tag>`; NegNum fue por otro camino (`lineWF_decide`,
  ADR‑154).
* **Los consumidores** (los `import`): sólo los cinco entre sí, el barril y el sondeo `IteSimboloNucleo`.

### 2 · Qué se hizo

1. **Los cinco, fuera del build.** Borrados; se recuperan de la etiqueta `archivo/t66-2026-10-18`, que apunta a
   `15dde2a`, el último commit con ellos (`git checkout archivo/t66-2026-10-18 -- ROBINSON_PlusPlus/Meta/X.lean`). Salen
   también sus 26 filas de footprint (24 de `ChainNegPrf`, una de `ChainDecode` y otra de `VerifierSound`) y la fila de
   avisos de `ChainNegPrf` (dos argumentos de `simp` sobrantes).
2. **`dec` frente a `decodeForm`** (lo que T76 dejaba a T66): queda `dec` (`Meta/SolidezVerificador.lean`), el
   decodificador de ℕ que usan W1(ax), NegNum y Rosser; `decodeForm` sale con `CodeDecode`.
3. **Los sondeos que usaban lo retirado:**
   - `IteSimboloNucleo` (CONTROL) copia las seis definiciones del decodificador, en el mismo espacio de nombres. Los
     59 teoremas dan lo mismo. En cinco de sus 23 bloques `#guard_msgs`, el mensaje del núcleo ya no imprime los tipos
     que nombran `decodeTerm.match_1`: con `pp.rawOnError`, «Unknown constant», porque el `match` se compila ahora en el
     propio fichero. Dice «failed to pretty print expression», y esos cinco mensajes fijados se actualizaron.
   - `OmegaConsistentRefutable` (CONTROL) copia `StdChain` y sus dos dependencias, y las §1ter y §1quater de
     `OmegaReflect`: `stdChain_proofCode'` y `junk_line_not_stdLine`. Son la «Verificación» de la regla M‑8, que pasa
     a citar este sondeo.
   - `DespachadorCoste` (REGISTRO), que medía el despachador de `ChainDecode`, se archiva con la misma etiqueta.
4. **Los sondeos de Rosser** (ADR‑146 §4.6, y lo que dejaron ADR‑151, ADR‑153 y ADR‑157):
   - `RosserBasura` se queda con §5, su control con el modelo. §1–§4, que el build ya cubre (ADR‑150, ADR‑153), salen;
     la versión entera está en la etiqueta.
   - `ExtensionPorReduccion` y `RosserHasWitF` pasan de CONTROL a REGISTRO: lo que vigilaban lo dice el build, con su
     `#pureza` (`Meta/Rosser.lean`; `prf_neg_hasWitF`, en `Meta/RosserGuardNeg.lean`).
   - `RosserReflexion` sigue de CONTROL: es el mutante de T08 que pasa por el modelo.
5. **`sondeos/ConoTitulares.lean`:** los 21 titulares; la fecha y la carpeta de salida, como datos; el control (2), con
   `Full/PrimeFactor.lean` (fuera del cono de imports) en lugar de `VerifierSound`.

### 3 · Lo medido

* **El build**, el 2026-10-18: 135 jobs y 118 módulos (Meta 113). `check-footprints`: 513 filas, todas cuadran.
  `check-warnings`: 9 avisos. Los 11 sondeos de control compilan. De los de REGISTRO, los cuatro que el grep de nombres
  señalaba (`ClausuraFormaEcuacional`, `RecodCoste`, `SymbolParam`, `SimbolosSinString`) también: eran homónimos.
* **El cono, re‑ejecutado tras la retirada** (`resumen-tras-T66.txt`): idéntico (4 416, 3 209, 31 103), con 18
  módulos sin nada en él. `Meta/` pasa de 53 669 a 50 711 líneas de fichero: las de los cinco y las cinco líneas de
  `import` del barril.
* **Sondeos:** 43 en el árbol (11 de CONTROL, 31 de REGISTRO, 1 a reparar) y 54 archivados.
* **`[A2]`**, el 2026-10-18: 22 avisos, frente a 37 antes de esta retirada. Las quince líneas históricas que dicen la
  cifra de jobs de hoy dejan de saltar; tres históricas de septiembre, con otra cifra, vuelven a saltar; y una de
  ADR‑159, que no llevaba fecha, ya dice «entonces». Ninguna es de este ADR.

### 4 · Lo que NO hace

* **No retira los demás que no aportan al cono:** `CodeDistinct`, `ReflectionPrf`, `Sigma1TrackedPrf`,
  `Sigma1BoundedPrf` (T05), `Full/PrimeFactor` y los ocho `import` de FOL (T74). Eso es el paso 3 de ADR‑139, que el
  propietario no ha aprobado. Tres de ellos los importan módulos del build.
* **«Fuera del cono» no es «borrable sin más»** (ADR‑139): lo que sólo sirve para elaborar no se ve. Aquí la prueba es
  el build y los sondeos de control, sin los cinco.

**Véase también:** ADR‑115 (la capa ⊢), ADR‑139 (el cono), ADR‑141 (los sondeos), ADR‑146 §4.6 y ADR‑147 (T66, al
final); T05, T66, T74 y T76 de la auditoría.

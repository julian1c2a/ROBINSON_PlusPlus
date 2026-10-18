# Next Steps — ROBINSON_PlusPlus

**Last updated:** 2026-10-18 — ADR‑161: el paso 3 de ADR‑139 en sus módulos, aprobado y hecho (cinco módulos sin nada en el cono, fuera del build; T05 cerrado en su retirada); lo siguiente, T78. Antes, el mismo día — ADR‑160: T66 hecho (el subárbol sin consumidor, fuera del build; los sondeos de Rosser, ordenados); lo siguiente, los P0/P1 abiertos de la auditoría y T78. Antes, el mismo día — ADR‑159: 🏁 Löb hecho (`lob` y `lob_iff`, en `Meta/Lob.lean`, de la clase (i), en `PUROS`); la línea de llegada, completa en sus teoremas; lo siguiente, T66 y los P0/P1 abiertos de la auditoría. Antes, el mismo día — ADR‑158: las decisiones sobre ADR‑157 (`rosser_ext` con `_hE`, el titular; `rosser`, titular). Antes, el mismo día — ADR‑157: 🏁 Rosser hecho (`rosser_ext` y `rosser_red`, de la clase (i), y `rosser`, de la (ii), en `Meta/Rosser.lean`; `rosser_ext`, en `PUROS`); lo siguiente, Löb (T70), y T66 al final. Antes, 2026-10-17 — ADR‑156: NegNum hecho (el predicado de prueba de T, decidido sobre numerales, y NegNum′ con W1(ax), `Meta/RosserNegNum.lean`, pura); lo siguiente, Rosser. Antes, el mismo día — ADR‑155: dos arreglos pendientes (el docstring de `consistencia`, relativa a Lean; `decMemN`, la pertenencia sin lógica clásica); lo siguiente, NegNum. Antes, el mismo día — ADR‑154: NegLineWF hecho (la buena formación de una línea, decidida sobre su numeral, `Meta/RosserNegLinea.lean`, pura); lo siguiente, NegNum. Antes, el mismo día — ADR‑153: GuardNeg hecho (la guarda falsa se refuta en `Prf` y queda decidida, `Meta/RosserGuardNeg.lean`, pura); lo siguiente, NegLineWF. Antes, el mismo día — ADR‑152: NumEval hecho (la sustitución sobre numerales con las guardas verdaderas, `Meta/RosserNumEval.lean`, pura); lo siguiente, GuardNeg. Antes, el mismo día — ADR‑151: el sondeo de `hasWitF`, verde (la puerta del riesgo, abierta); lo siguiente, NumEval. Antes, el mismo día — ADR‑150: la capa de listas sobre numerales, hecha (`Meta/RosserNumerales.lean`, pura); lo siguiente, el sondeo de `hasWitF`. Antes, el mismo día — ADR‑149: PosNum hecho (`posNum`, en `Meta/RosserPosNum.lean`, puro) y T08 sigue los lemas del propio módulo; lo siguiente, la capa de listas. Antes, el mismo día — ADR‑148: W1(ax) hecho (`w1Ax`, en `Meta/RosserW1.lean`, puro); lo siguiente, PosNum. Antes, el mismo día — ADR‑147: el diseño de NegNum y PosNum, decidido (las tres recomendaciones de ADR‑146); lo siguiente, W1(ax). Antes, 2026-10-16 — ADR‑146: el diseño de NegNum y PosNum, propuesto. Antes, el mismo día — ADR‑145: Rosser por REDUCCIÓN, decidido; lo siguiente, NegNum y PosNum de T. Antes, el mismo día — ADR‑144: el ADR de diseño de T62, propuesto. Antes, el mismo día — ADR‑143: T08 hecho (el control de pureza, en el build). Antes, el mismo día — ADR‑142: este fichero, a una página (los bloques viejos, en doc/historia/), con la lista «Pendiente además de Rosser» (T36). Antes, el mismo día — ADR‑141: los sondeos (11 de control en la CI, 53 archivados). Antes, el mismo día — ADR‑140: las decisiones del propietario (capas dentro de RPP, la línea de llegada, ADR‑139 aprobado en sus pasos 1 y 2). Antes, el mismo día — ADR‑138: la consistencia es RELATIVA a Lean; ADR‑139, PROPUESTO: el plan para acotar el proyecto, con el cono de los titulares medido. Antes, 2026-10-14 — ADR‑137: Rosser, decidido (la teoría como parámetro del verificador + T08). Antes, el mismo día — ADR‑136: `master` protegido (T14) y las decisiones del propietario del día. Antes, el mismo día — ADR‑135: T09 hecho (`TEOREMAS-E-HIPOTESIS.md` al día, con la columna «¿qué usa la prueba?» medida, y el control `[T]`). Antes, el mismo día — ADR‑134: T02 hecho (la teoría de los titulares, `T_Prf`, descrita en `AXIOMS.md` §0: contiene a PA; y dónde entra la inducción, medido: `sondeos/InduccionTitulares.lean`), con su revisión adversarial y los comentarios de los `.lean` al día (T31). Antes, 2026-10-12 — ADR‑133: T03 hecho (la tabla MANDATORIES y el control `[M]`). Antes, 2026-10-12 — ADR‑132: la auditoría del suelo, versionada (`doc/AUDITORIA-SUELO-2026-10-12.md`, 81 trabajos: es la lista de trabajo vigente; bloque nuevo, arriba) y T00 hecho. Antes, 2026-10-05 — ADR‑131: el `Classical.choice` de los titulares, medido (punto 6, nuevo); ADR‑130: las dos notas de `Meta/CodeDecode.lean`, medidas (punto 5, hecho); ADR‑129: D7 EJECUTADA (punto 2, hecho); ADR‑128: `autoImplicit` desactivado también en `lake build` (punto 4, hecho); ADR‑127: la auditoría de ADR‑124/125/126 (el punto 1, rectificado) y los 88 sondeos re‑medidos (35 compilan); ADR‑126: la refutación a profundidad 2 y el control de discriminación (`sondeos/RosserBasura.lean`, punto 1); ADR‑125: la guarda de término refutada sobre un numeral (`sondeos/RosserBasura.lean`, punto 1); ADR‑124: el control negativo del modelo, en el build (punto 3, hecho), y la auditoría de ADR‑123 (el punto 1, rectificado); ADR‑123: Rosser, Etapa 0 —la reflexión numeral, confirmada en `sondeos/RosserReflexion.lean`—; ADR‑122: D7 medida (la puerta dice NO: 48 de 226) y Rosser re‑medido; ADR‑121: Gödel I ENTERO (`⊬ ¬G`) y TARSKI, sin hipótesis (bloque nuevo, arriba). Antes, 2026-10-05 — ADR‑120: `ConsistentH` es un TEOREMA del build y Gödel I/II van SIN HIPÓTESIS (bloque nuevo, arriba). Antes, 2026-10-05 — ADR‑119: el MODELO de los 142, `ConsistentH` demostrada en un sondeo (bloque nuevo, arriba); lo siguiente, su promoción al build. Antes, 2026-10-05 — ADR‑118: la clase `AnclaEq` retirada; lo siguiente, el modelo de los 142. Antes, 2026-10-04 — ADR‑117: F1 reparado, el ancla es un TEOREMA y Gödel I/II dependen sólo de `ConsistentH` (bloque nuevo, arriba); lo siguiente, retirar la clase `AnclaEq`. Antes, el mismo día — ADR‑116: los controles endurecidos, el `thaw` de FOL hecho y la etiqueta `pre-adr115` puesta (bloque nuevo, arriba); lo siguiente es F1. Antes, 2026-10-02 — FOL borró `FOL/MetaRules.lean` (ADR‑115 §8): el punto 1 de la lista, hecho; los sondeos, re‑medidos (31 de 85). Antes, el mismo día — ADR‑115: la capa `⊢` retirada de RPP (bloque de abajo, y la lista de lo que queda). Antes, 2026-09-28 — ADR‑113: la salida (5) adoptada y aplicada (bloque de abajo). Antes, 2026-09-26 — `Prf₀` → `Prfᵢ` en todo el fichero (ADR-102: el subíndice nombra un cálculo, y `₀` es el clásico); y se tachan, en el bloque del 2026-09-22, las dos menciones a la 2.ª entrega de `ModelG` (CERRADA, ADR-100 §1.1; definitiva el 2026-09-26); el resto sigue siendo el del 2026-09-22 y **no recoge ADR-098…100**. El bloque fechado más reciente manda. ⚠️ La marca que este fichero tenía decía **2026-07-08** y vivía en la **línea 3763**, donde nadie la ve ni la actualiza; lo destapó `[E]` al rearmarse (ADR-072). Esta va arriba, que es donde se lee.

---

## ▶ PUNTO DE REANUDACIÓN (leer PRIMERO)

> # 🗓️ 2026‑10‑12 — 📋 **ADR‑132: la lista de trabajo vigente es `doc/AUDITORIA-SUELO-2026-10-12.md`**
>
> 81 trabajos priorizados con su evidencia y cómo cerrarlos. **P0**: T01 (Rosser: un enunciado con contenido antes
> de pagarlo; decide el propietario), T02 (la teoría `T_Prf` descrita con precisión; ✅ ADR‑134: contiene a PA, `AXIOMS.md` §0), T03 (MANDATORIES: M‑11, M‑10 y
> M‑6; ✅ ADR‑133), T04 (el núcleo de `[B]`). **P1**: T00 (✅ ADR‑132), T04b, T06, T07, T08, T09 (✅ ADR‑135), T15. Orden recomendado:
> T03 (✅) → T02 (✅) → T09 (✅) → T01 (decisión) → T08 → T04 → T06 → … Medido el 2026‑10‑12 (retirados en ADR‑161): `d3_prf_of_sigma1` y
> `d3_prf_of_reflect_bounded` son VACUOS (`sondeos/D3Sigma1Vacuo.lean`; T05, P2; retirados en ADR‑161). Y D1 usa la inducción, D2 la de
> listas, y ningún titular construye un paso DNE salvo `goedel_I_neg`, al decodificar el modelo
> (`sondeos/InduccionTitulares.lean`; ADR‑134).
>
> 🗓️ **2026‑10‑14 — decisiones del propietario** (ADR‑136): T26 y T28 se REESCRIBEN; T49 (el libro), vivo y en espera;
> T14: `master` PROTEGIDO —sólo entra un commit con la CI ya verde, por una rama `ci/…` (AI‑GUIDE, `guarda_y_sube`)—, y
> un módulo de RPP se congela sólo con su fase cerrada (hoy, ninguno). T01 (Rosser), DECIDIDO por la tarde (ADR‑137):
> **la teoría como parámetro del verificador** (opción a‑ii), con **T08** como criterio de aceptación; el informe, en
> `doc/registro/2026-10-14-t01-rosser/informe.md`. Lo siguiente: **T08** → la medición de alcance y el ADR de diseño de
> T62 (ii) → el sondeo de viabilidad de Rosser; y T04, T06 y las reescrituras de T26 y T28.
>
> 🗓️ **2026‑10‑16** — ADR‑138: la consistencia que da `consistencia` es RELATIVA a Lean (PRA ⊢ Con(Lean) → Con(T_Prf))
> y no puede ser absoluta; dicho en los banners, en `TEOREMAS-E-HIPOTESIS.md` §4, en `AXIOMS.md` §0.2 y en
> `PLAN-LIBRO.md` cap. 6. ADR‑139, 🟡 PROPUESTO (decide el propietario): acotar el proyecto en tres pasos —archivar los
> sondeos (T06 → T10), congelar la historia (T33, T36, T54, T55) y contratos de capa (T66, T74)—, con el cono de los
> titulares MEDIDO por declaración (`sondeos/ConoTitulares.lean`: D3 es el 92 % del cono; lo que sobra no está en el
> build, sino en los sondeos y en la prosa). Mientras no se decida, el orden de ADR‑137 sigue en pie.
> ✏️ Decidido el mismo día (ADR‑140): capas DENTRO de RPP (un repositorio aparte sólo al cerrar una capa; Gentzen, en
> el suyo); la línea de llegada de RPP es `T_UNIVERSO` + Rosser + Löb, y Gentzen y el libro quedan fuera; las variantes
> Q++/PA/HA se miden en el diseño de T62. ADR‑139 aprobado en sus pasos 1 (sondeos) y 2 (historia), que se ejecutan
> ahora; después, el orden de ADR‑137 (T08 → T62).
> ✏️ ADR‑141 (paso 1, hecho): los sondeos, medidos con `lake lean` (39 de 93 compilan) y clasificados: 11 de control,
> que la CI compila en cada push; 28 de registro; 1 a reparar; y 53 archivados con la etiqueta `archivo/sondeos-2026-10`.
> ✏️ ADR‑142 (paso 2, hecho): la historia, a `doc/historia/` por traslado puro: ADR‑001…130 (en DECISIONS queda su
> índice), los bloques viejos de este fichero y los banners apilados; la fuente única del estado es el banner de
> `TEOREMAS-E-HIPOTESIS.md`; CHANGELOG, congelado.
> ✏️ ADR‑143: T08, el control de pureza, en el build. ADR‑144 y ADR‑145: el diseño de T62, DECIDIDO: Rosser por
> REDUCCIÓN (T+E es `PrfH E`; su predicado de prueba, el de T delante de `impChain`), sin tocar el verificador ni los
> 142; V‑B si alguna vez hace falta un verificador con parámetro; las variantes de reglas, aplazadas. Lo siguiente:
> NegNum y PosNum de T.
> ✏️ ADR‑146 (PROPUESTO): el diseño de NegNum y PosNum. Medido: de las 80 piezas del build que el plan reutiliza, 76
> son PURAS (T08); W1 sólo es impuro por `linea_thy`, y se arregla enunciándolo con `codeNatList axioms`; PosNum sale
> de D1 y un lema; el orden propuesto pone el riesgo (la guarda `hasWitF`) pronto.
>
> 🗓️ **2026‑10‑17** — ADR‑147: las decisiones del propietario sobre ADR‑146 (su respuesta, del 16 por la noche, no
> llegó a procesarse y se registra hoy): el orden de su §4, con el sondeo de `hasWitF` pronto; el código en el build,
> con un `#pureza` al final de cada módulo; T66, al final. Lo siguiente: **W1(ax)**, en `Meta/RosserW1.lean`.
> ✏️ ADR‑148: **W1(ax), hecho.** La cadena de W1 es paramétrica en `V` (`Bueno V`) y `w1Ax` la instancia con el
> código de los 142, sin el modelo: PURO por su `#pureza`, con `verificador_solido` como control positivo (IMPURO).
> Entonces, 131 jobs y 114 módulos. Lo siguiente: **PosNum** (ADR‑146 §3, etapa 6).
> ✏️ ADR‑149: **PosNum, hecho.** `prf_proofCode'_numeral` (el término de prueba de D1 es el numeral de su valor) y
> `posNum : Prf φ → ∃ m, Prf (PfF m̄ ⌜φ⌝)`, puro. Por el camino, T08: el `#pureza` por módulo no seguía los lemas del
> propio módulo (medido con un mutante); arreglado, y `mutanteLocal` lo vigila en cada build. Entonces, 132 jobs y
> 115 módulos. Lo siguiente: **la capa de listas sobre numerales** y, justo después, el sondeo de `hasWitF`.
> ✏️ ADR‑150: **la capa de listas, hecha.** Sobre numerales, `Prf` descompone (`m̄ = cons ⟨carN m⟩‾ ⟨cdrN m⟩‾`), evalúa
> `carc`/`cdrc`/`lenc`/`nthc`, `concat`, `runFn` y los constructores de código, y decide `In` en los dos sentidos,
> también en las conclusiones de una cadena. Pura. Entonces, 133 jobs y 116 módulos. Lo siguiente: **el sondeo de
> `hasWitF`**, la puerta del riesgo, antes de NumEval y NegLineWF.
> ✏️ ADR‑151: **el sondeo de `hasWitF`, verde** (`sondeos/RosserHasWitF.lean`, de CONTROL). La guarda de fórmula se
> refuta sobre numerales basura a profundidad 1 y 2, en casilla de fórmula y en casilla de término, sin el modelo; el
> `∃∃` costó dos `prf_ex_elim_imp`. La puerta del riesgo se abre. Lo siguiente: **NumEval**.
> ✏️ ADR‑152: **NumEval, hecho.** Sobre numerales, `Prf` evalúa `substtc` y `liftc` (y sus listas), `substfc` y
> `liftfc` como sus espejos de ℕ, sobre los códigos buenos (`CodT`, `CodF`); y las guardas de las líneas dan códigos
> buenos: `prf_substfc_guarda`. Pura. Entonces, 134 jobs y 117 módulos. Lo siguiente: **GuardNeg** (la caracterización
> en ℕ y la hereditaria general).
> ✏️ ADR‑153: **GuardNeg, hecho.** Donde la guarda es falsa en ℕ, `Prf` la refuta entera: `prf_neg_hasWit` y
> `prf_neg_hasWitF`, por una dicotomía constructiva (inducción fuerte en el número: código bueno, o fuera de toda lista
> testigo), con la caracterización en ℕ completa (`hasWitN c ↔ CodT c`). Pura, sin `Classical.choice`. Entonces, 135
> jobs y 118 módulos. Lo siguiente: **NegLineWF**.
> ✏️ ADR‑154: **NegLineWF, hecho.** La buena formación de una línea, decidida sobre su numeral: `lineWF_decide :
> lineWFN Vax x ∨ Prf ¬lineWF x̄`, por la inversión y las 21 reglas, con las guardas por GuardNeg, la sustitución por
> NumEval y `thy` por el ancla. Pura. Entonces, 136 jobs y 119 módulos. Lo siguiente: **NegNum** (la cadena y las
> premisas).
> ✏️ ADR‑155: dos arreglos pendientes, el docstring de `consistencia` (relativa a Lean, ADR‑138) y `decMemN` (la
> pertenencia sin lógica clásica).
> ✏️ ADR‑156: **NegNum, hecho.** El predicado de prueba de T, decidido sobre numerales: `proofN_decide : ProofN m y ∨
> Prf ¬PfF m̄ ȳ`, la cadena línea a línea con `lineWF_decide` y las premisas de `mp`/`gen`; y con W1(ax), `negNum'`: si
> φ no es teorema, T refuta cada candidata a prueba de φ. Pura. Entonces, 137 jobs y 120 módulos. Lo siguiente:
> **Rosser** (etapa 7, por la reducción).
>
> 🗓️ **2026‑10‑18** — ADR‑157: **🏁 ROSSER, hecho**, por la reducción (`Meta/Rosser.lean`). `rosser_ext`: si T+E es
> consistente, su sentencia de Rosser es indecidible en T+E; `rosser_red`, lo mismo para toda lista E (la hipótesis de
> que E son sentencias, `hE`, no la usa la prueba: sólo hace de `PrfH E` la teoría T+E); y `rosser`, para T, sin
> hipótesis. `rosser_ext` es de la clase (i) y entra en `PUROS` de T08, y `rosser` en `IMPUROS`: para eso, el recorrido
> y `#pureza` pasan a `Meta/PurezaComando.lean`. Visto fallar en los dos sentidos con tres mutantes. Entonces, 139 jobs
> y 122 módulos. Lo siguiente: **Löb** (T70), y **T66** al final (ADR‑147).
> ✏️ ADR‑158: las decisiones del propietario sobre ADR‑157: `rosser_ext`, con `_hE`, sigue de titular, y `rosser_red`
> es la forma más fuerte; `rosser`, titular.
> ✏️ ADR‑159: **🏁 LÖB, hecho** (`Meta/Lob.lean`): `lob : Prf (Prov⌜φ⌝ ⇒ φ) → Prf φ` y `lob_iff`, por el punto fijo
> de Prov(#0) ⇒ φ y D1–D3; Gödel II sale de él con φ = ⊥ (`goedel_second_de_lob`). De la clase (i), en `PUROS`. Con
> él, **la línea de llegada de RPP (ADR‑140) está completa en sus teoremas**. Entonces, 140 jobs y 123 módulos. Lo
> siguiente: **T66** y los P0/P1 abiertos de la auditoría (T04, T04b, T07, T15); los corolarios de T78.
> ✏️ ADR‑160: **T66, hecho.** Medido con el cono de los 21 titulares, el subárbol sin consumidor —`ChainNegPrf`,
> `VerifierSound`, `OmegaReflect`, `ChainDecode`, `CodeDecode`: 2 953 líneas, ninguna declaración en el cono; Rosser no
> heredó nada de él— sale del build, con la etiqueta `archivo/t66-2026-10-18`; `dec` se queda, `decodeForm` sale. Los
> sondeos de Rosser: `RosserBasura`, con su §5; `ExtensionPorReduccion` y `RosserHasWitF`, a REGISTRO; `DespachadorCoste`,
> archivado. Entonces, 135 jobs y 118 módulos. Lo siguiente: los P0/P1 abiertos de la auditoría y T78.
> ✏️ ADR‑161: el propietario aprueba el paso 3 de ADR‑139 en sus módulos: `CodeDistinct`, `ReflectionPrf`,
> `Sigma1TrackedPrf`, `Sigma1BoundedPrf` y `Full/PrimeFactor` salen del build (742 líneas, nada en el cono; etiqueta
> `archivo/fuera-del-cono-2026-10-18`), y con ellos los dos teoremas vacuos de T05. Entonces, 130 jobs y 113 módulos.
> Lo siguiente: **T78**.
>
> 🗓️ *Los bloques anteriores (del 2026‑10‑05 hacia atrás) y las secciones de junio y julio están, tal cual, en
> [doc/historia/NEXT-STEPS-hasta-2026-10-14.md](doc/historia/NEXT-STEPS-hasta-2026-10-14.md) (ADR‑142).*

---

## ⬜ Pendiente además de Rosser (T36)

✏️ 2026‑10‑18 (ADR‑157): Rosser, hecho; la sección conserva su nombre, el de T36.

**Regla:** un punto sale de esta lista sólo CERRADO con su ADR, o DESCARTADO con una nota fechada. La lista entera,
con su evidencia y cómo cerrar cada punto, es `doc/AUDITORIA-SUELO-2026-10-12.md`.

* **El orden de ADR‑137:** ~~T08~~ ✅ (ADR‑143: el control de pureza, en el build) → ~~el ADR de diseño de T62~~ ✅
  (ADR‑144, aceptado en ADR‑145: Rosser por REDUCCIÓN, T+E es `PrfH E`) → **NegNum y PosNum de T**, por la ruta
  sintáctica (diseño: ADR‑146, aceptado en ADR‑147: en el build, con un `#pureza` por módulo; ~~W1(ax)~~ ✅ ADR‑148 →
  ~~PosNum~~ ✅ ADR‑149 → ~~listas~~ ✅ ADR‑150 → ~~sondeo de `hasWitF`~~ ✅ ADR‑151 → ~~NumEval~~ ✅ ADR‑152 →
  ~~GuardNeg~~ ✅ ADR‑153 → ~~NegLineWF~~ ✅ ADR‑154 → ~~NegNum~~ ✅ ADR‑156) → ~~Pf_E y su transporte~~ →
  ~~`rosser_ext`, en `PUROS` de T08~~ ✅ ADR‑157 (`Meta/Rosser.lean`).
* ~~**Löb** (T70)~~ ✅ ADR‑159 (`Meta/Lob.lean`): la línea de llegada de RPP, completa en sus teoremas.
* **T78**, los corolarios baratos: `Prf (G ⇔ Con')`, `¬ Prf ¬Con'` y Gödel II formalizado (ESTIMACIÓN de la
  auditoría: 30–80 líneas).
* ~~**T66**~~ ✅ ADR‑160: el subárbol sin consumidor, fuera del build; los sondeos de Rosser, ordenados.
* **ADR‑139, paso 3:** ~~los módulos de RPP sin nada en el cono~~ ✅ ADR‑161; quedan los ocho `import` de FOL (T74),
  que piden su propia decisión (alguno hace falta para elaborar).
* **Los P0 y P1 abiertos de la auditoría:** T04 (el núcleo de `[B]`), T04b (`[A]` y `[A2]` ciegos), T07 (el contrato de
  los enunciados y de los valores de las definiciones) y T15 (todo `.lean` del árbol en el build).
* **ADR‑139, paso 3:** las capas dentro de RPP (ADR‑140), con los 21 ficheros importados que no aportan nada al cono
  (T05, T66, T74).
* **Lo que se había caído de las listas** (T36): la ronda 3 y la revisión adversarial de D7 (T17), la deuda de ADR‑115
  §5 (`DEPENDENCIES.md`) y promover cuatro de `Probe/` y barrer el resto (T48).
* **Las reescrituras** de `CURRENT-STATUS-PROJECT.md` y `GODEL-STATUS.md` (T26, T28).

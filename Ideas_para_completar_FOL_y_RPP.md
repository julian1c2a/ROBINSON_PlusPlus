# Ideas para completar FOL y RPP

**Last updated:** 2026-10-19 — notas del propietario, tal cual (la cabecera, añadida porque `[E]` pide una marca de tiempo en todo `.md` del repo).

Hemos completado en ROBINSON_PlusPlus el Primer y Segundo Teorema de Incompletitud de Gödel (Godel.lean, GodelTwo.lean), el Teorema de Rosser (Rosser.lean), el Teorema de Löb (Lob.lean) y la Indefinibilidad de Tarski (TarskiPrf.lean), y además haber construido en FOL toda la maquinaria sintáctica y semántica de FOL= (Deducción Natural, Cálculo de Secuentes LK, Eliminación de Corte / Hauptsatz, Completitud de Henkin, Compacidad, Herbrand, Skolemización e Interpolación de Craig) con una auditoría estricta de axiomas constructivos vs. clásicos (Classical.choice) y cero sorrys, supera con creces un proyecto de aprendizaje personal.  

A continuación, divido mi análisis en dos partes: 1) Qué más puedes hacer para enriquecer tu repositorio de FOL= y 2) Cómo enfocar una contribución real y exitosa a Mathlib.

# Parte 1: ¿Qué más se puede hacer sobre tu base de FOL=?

Dado que en tu repositorio FOL ya tienes Completitud (Canonical0 / Henkin0), Eliminación de Corte (Hauptsatz0), Herbrand (Herbrand0) e Interpolación de Craig (Craig0), tienes los cimientos perfectos para demostrar los grandes teoremas puente entre la Teoría de la Demostración y la Teoría de Modelos que rara vez están formalizados de forma sintáctica/constructiva:   

1. Consecuencias directas de la Interpolación de Craig (Muy bajo coste para ti ahora mismo)

Ya tienes Craig0.lean y Interpolation0.lean. En la literatura clásica de lógica matemática, de Craig se deducen casi inmediatamente dos teoremas célebres que enriquecerían muchísimo tu librería:

    1.1. **Teorema de Definibilidad de Beth** (Beth's Definability Theorem): Si una teoría define implícitamente un nuevo símbolo de predicado P (es decir, cualquier modelo de la firma base tiene a lo sumo una extensión que satisface la teoría con P), entonces existe una fórmula explícita en el lenguaje base que es demostradamente equivalente a P(x) (definibilidad explícita). Su demostración es una aplicación directa de la Interpolación de Craig.

    1.2. **Teorema de Consistencia Conjunta de Robinson** (Robinson's Joint Consistency Theorem): Si dos teorías T1​ y T2​ en lenguajes L1​ y L2​ son consistentes y su intersección T1​∩T2​ es completa en el lenguaje común L1​∩L2​, entonces T1​∪T2​ es consistente. Es equivalente a Craig y a Compacidad combinados.

2. Teoremas de Preservación (Teoría de Modelos Sintáctica)

Con Compacidad, Completitud y Formas Normales Prenexas (PrenexNF0.lean), puedes atacar los teoremas clásicos de caracterización sintáctica de propiedades semánticas:

    2.1. Teorema de Łoś-Tarski: Una fórmula (o teoría) se preserva bajo subestructuras si y solo si es equivalente a una fórmula universal (Π10​ en la jerarquía de cuantificadores).

    2.2. Teorema de Lyndon: Una fórmula es monótona respecto a un símbolo de relación R si y solo si es equivalente a una fórmula donde R solo aparece positivamente (puedes aprovechar la maquinaria de polaridad que ya sueles usar en secuentes e interpolación).

    2.3. Teorema de Chang-Łoś-Suszko: Caracterización de las teorías que se preservan bajo uniones de cadenas (inductivas) como exactamente las teorías axiomatizables mediante sentencias ∀∃ (Π20​).

3. Teoría de Modelos clásica: Löwenheim-Skolem y Omitir Tipos

    3.1. Löwenheim-Skolem Descendente y Ascendente: Tu prueba de Henkin (Henkin0.lean, HenkinLimit0.lean) y la enumeración de fórmulas (Enumeration.lean) ya construyen de facto un modelo numerable (o del cardinal del lenguaje) sobre las constantes de Henkin. Explicitar el teorema de Löwenheim-Skolem como corolario directo de tu construcción canónica es un paso muy natural.

    3.2. Teorema de Omisión de Tipos (Omitting Types Theorem): Una generalización preciosa del método de Henkin donde, además de añadir testigos existenciales paso a paso, se diagonaliza contra un conjunto numerable de tipos no principales (no aislados) para construir un modelo que los omita.

    3.3. Teorema de Lindström: El teorema que caracteriza a FOL= como la lógica maximal que cumple simultáneamente el teorema de Compacidad y el teorema de Löwenheim-Skolem descendente. Tienes TheoryFramework/Logic.lean y MetaTheorems.lean diseñados precisamente como un marco abstracto de lógicas; Lindström sería la joya de la corona para justificar la existencia de TheoryFramework.

4. Conectar por completo FOL y ROBINSON_PlusPlus (Lógica de la Demostrabilidad)

Ya tienes un documento ENGARCE-ROBINSON-FOL.md y en ROBINSON_PlusPlus tienes Lob.lean.

    4.1. Completitud Aritmética de Solovay (Lógica Modal GL): Dado que tienes el predicado de demostrabilidad con las condiciones de Hilbert-Bernays-Löb (DerivCondPrf.lean) y el teorema de Löb (Lob.lean), puedes formalizar el fragmento de lógica modal provabilidad GL (Gödel-Löb) y mostrar cómo sus axiomas se interpretan en tu verificador de ROBINSON_PlusPlus.

    4.2. Eliminación de Cuantificadores en teorías concretas: Usar FOL para instanciar una teoría decidible (como órdenes lineales densos sin extremos DLO o aritmética de Presburger) y probar su completitud/decidibilidad mediante eliminación de cuantificadores (conectando con QFDecide0.lean).   
    ZIP

# Parte 2: Cómo hacer una contribución de código a Mathlib

Contribuir a Mathlib4 tiene una particularidad importante: Mathlib no acepta "volcados" de repositorios externos con definiciones paralelas, sino que exige integrarse en las estructuras que ya existen en Mathlib/ModelTheory/.
¿Qué hay actualmente en Mathlib y qué le falta?

En Mathlib4 existe el directorio Mathlib.ModelTheory (desarrollado originalmente en el proyecto Flypitch por Jesse Han y Floris van Doorn, y mantenido hoy por Aaron Anderson, entre otros).

    1. Lo que Mathlib YA TIENE (Semántica): Define FirstOrder.Language, Term, BoundedFormula, Formula (usando índices de De Bruijn / Fin n junto con variables libres tipadas), estructuras, homomorfismos, incrustaciones elementales, ultraproductos, el Teorema de Compacidad (vía ultraproductos / filtros), Löwenheim-Skolem y cuantificadores / eliminación de cuantificadores básica.

    2. Lo que a Mathlib LE FALTA (¡Tu especialidad: Sintaxis y Teoría de la Demostración!): Mathlib4 es muy rico en Teoría de Modelos semántica, pero está casi vacío en Teoría de la Demostración (Proof Theory) y metateoría sintáctica. No tiene cálculo de secuentes (LK), no tiene eliminación de corte (Hauptsatz), no tiene el teorema de Herbrand, no tiene interpolación de Craig, no tiene Skolemización sintáctica constructiva y no tiene los teoremas de incompletitud de Gödel ni la jerarquía aritmética Δ0​/Σ1​ integrada.

(Nota sobre el ecosistema Lean 4: Existe un proyecto externo muy conocido llamado FormalizedFormalLogic / Foundation deieh/kogai en Japón que también trabaja en Gödel/Secuentes fuera de Mathlib, pero en el propio tronco de Mathlib4 todo ese hueco sigue abierto).
4 Ideas concretas de PRs (Pull Requests) para Mathlib4

Si quieres que tus PRs sean revisados rápido y aceptados con entusiasmo por los mantenedores de Mathlib, te sugiero ir de menor a mayor fricción arquitectónica:

    3.1. Idea de PR #1 (Entrada rápida y muy valorada): Forma Normal Prenexa y Skolemización sobre FirstOrder.Language.BoundedFormula

        3.1.1. En tu repo tienes Prenex0.lean, PrenexNF0.lean, Skolem0.lean y SkolemNF0.lean.

        3.1.2. Si miras Mathlib/ModelTheory/Syntax.lean y Semantics.lean, verás cómo definen BoundedFormula. Traducir tus algoritmos de conversión a Forma Normal Prenexa y la equivalencia semántica a las definiciones de Mathlib.ModelTheory sería un PR autocontenido (de unas 200-400 líneas por archivo), muy limpio y que los mantenedores de ModelTheory revisarían sin dudar.

    3.2. Idea de PR #2 (Impacto medio-alto): Sistema deductivo sintáctico (Hilbert / Deducción Natural / Secuentes) + Completitud de Henkin constructiva para Mathlib.ModelTheory

        3.2.1. En Mathlib4, la compacidad se prueba semánticamente con ultraproductos (usando fuertemente el axioma de elección / lema de Zorn sobre ultrafiltros). Mathlib no tiene una relación de derivabilidad sintáctica T ⊢ φ conectada con T ⊨ φ (el Teorema de Completitud de Gödel propiamente dicho).

        3.2.2. Tú ya has hecho toda la ingeniería difícil en Derives0.lean, Henkin0.lean, Lindenbaum0.lean y Canonical0.lean, además de tener clarísimo dónde interviene exactamente Classical.choice gracias a tu auditoría del 27 de septiembre (auditoria/constructividad-2026-09-27). Adaptar tu prueba de completitud de Henkin al tipo FirstOrder.Language.Formula de Mathlib sería una contribución histórica a la librería.

    3.3. Idea de PR #3 (Brillante y único): Cálculo de Secuentes LK, Eliminación de Corte (Hauptsatz) y Teorema de Interpolación de Craig / Herbrand

        3.3.1. Hauptsatz0.lean, Herbrand0.lean y Craig0.lean son algoritmos puramente sintácticos y finitistas.

        3.3.2. Una vez exista el puente con las fórmulas de Mathlib (o proponiendo un subdirectorio Mathlib/ModelTheory/ProofTheory/ o Mathlib/Logic/ProofTheory/), aportar la eliminación de corte de Gentzen y usarla para demostrar constructivamente el Teorema de Interpolación de Craig y el Teorema de Herbrand (y como corolario el Teorema de Definibilidad de Beth en ModelTheory) daría a Mathlib toda una rama de la lógica que hoy no posee.

    3.4. Idea de PR #4 (Utilidades generales / Bajo nivel): Lemas de Nat, List, codificación de Cantor y tácticas/linters

        3.4.1. En ROBINSON_PlusPlus/Meta/CantorMonoPrf.lean, Div2ParityPrf.lean, NatArithPrf.lean y en tus scripts de auditoría (sondeos/lintlab/AxLinter.lean, VolcarEntorno.lean) has demostrado un montón de lemas sobre emparejamiento de Cantor (Nat.pair / Nat.unpair en Mathlib), monotonía e inyectividad de codificaciones de árboles/listas.

        3.4.2. Muchos lemas de cotas finitas sobre Nat.pair o sobre inyectividad de codificaciones en Mathlib/Data/Nat/Pairing.lean pueden faltar o ser mejorables. Hacer un primer PR pequeño añadiendo 3 o 4 lemas útiles a Data.Nat.Pairing es la mejor forma de "romper el hielo" con el proceso de CI, estilo de código y revisión de Mathlib antes de lanzar un PR grande de Lógica.

Recomendación estratégica (Hoja de ruta hacia Mathlib)

    3.5. No intentes migrar tu sintaxis propia (SymLit, variables con Nat/strings) directamente a Mathlib: En Mathlib son muy estrictos con que todo resultados de primer orden use FirstOrder.Language.BoundedFormula L α n (que es polimórfica en la firma L y los tipos de variables).

    3.6. Construye un archivo "Puente" (MathlibBridge.lean) en tu repo FOL: Añade Mathlib como dependencia en una rama experimental (o un subproyecto) y define una traducción (isomorfismo sintáctico y semántico) entre tu FOL.Formula (cuando se instancia en una firma concreta) y FirstOrder.Language.Formula de Mathlib.

        3.6.1. Si demuestras que tu noción de satisfacibilidad coincide con FirstOrder.Language.Formula.Realize de Mathlib, puedes transportar inmediatamente tus teoremas (Craig, Herbrand, Completitud, Gödel) a los tipos de Mathlib casi sin reescribir tus pruebas internas, o bien usar esa experiencia para portar los módulos uno a uno al estilo nativo de Mathlib.

    3.7. Pásate por el Zulip de Lean (#Is there code for X? o #maths > Model theory): Comenta en el stream de Model Theory que tienes formalizados en Lean 4 (v4.31.0, sin sorrys) la Eliminación de Corte (LK), Herbrand, Interpolación de Craig, Completitud de Henkin y Gödel I/II/Rosser/Löb, y pregunta a los mantenedores de Mathlib/ModelTheory cómo prefieren estructurar la carpeta de ProofTheory / Syntax para ir enviando PRs pequeños.

¿seguir ampliando metateoría en FOL (como Beth, Łoś-Tarski o Lindström)? o ¿preparar un primer acercamiento/puente hacia Mathlib.ModelTheory?
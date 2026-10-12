export const meta = {
  name: 'auditoria-base-ronda-2',
  description: 'Ronda 2 de auditorías de la BASE, sobre master con ADR-113: consistencia, retiro de ⊢ y MetaRules, arreglo de F1, FOL como base y crítico de completitud (sólo lectura, sin compilar)',
  phases: [
    { title: 'Auditoría', detail: 'cinco lentes sobre la base reparada' },
    { title: 'Verificación', detail: 'un verificador adversarial por lente' },
  ],
}

const ART = '<sesión>/artefactos-ronda1'

const CONTEXTO = [
  '# Auditoría de la BASE — ronda 2 (2026-10-02)',
  '',
  'Eres auditor de un proyecto de lógica formal en Lean 4 (v4.31.0, SIN Mathlib). Responde en español.',
  '',
  '## El proyecto',
  '* RPP = ROBINSON_PlusPlus, en E:/dropbox/github/lean4/ROBINSON_PlusPlus, rama master, que YA incluye ADR-113 (cons a b = σ (pair a b); fusionado hoy). Formaliza Gödel I y II para una teoría aritmética de 141 axiomas = 34 «core» + 107 «de codificación» (ROBINSON_PlusPlus/Minimal/Axioms.lean). El verificador de pruebas está DENTRO de la teoría (validProofFn, lineWF, premsOf, substfc, liftfc, carc, lenc, nthc, tcFn…, definidos por los axiomas de codificación).',
  '* Dos cálculos: `⊢` = `Derives` de FOL con los 4 `axiom` de FOL/FOL/MetaRules.lean y los 3 `axiom` de RPP (ax_induction_prim, ax_list_induction, ax_axiomsCodeT_eq); y `Prf` (⊢ᴴ, Hilbert propio de RPP, ROBINSON_PlusPlus/Meta/Hilbert.lean). Gödel I/II sobre Prf: Meta/GodelTwoPrf.lean:187 y :196.',
  '* FOL = E:/dropbox/github/lean4/FOL (primer orden con igualdad): capa herramienta (Derives + MetaRules) y capa ₀ (Derives₀: deducción natural clásica, sólida y completa, sin axiomas del proyecto). RPP importa sólo 9 módulos de la capa herramienta. 23 módulos de FOL están congelados (frozen_files.txt).',
  '* PeanoRF (E:/dropbox/github/lean4/Peano-from-ROB-n-FOL) está BLOQUEADO por el propietario: sólo lectura, y sólo como consumidor.',
  '',
  '## Lo que dejó la ronda 1 (no lo repitas como nuevo; sí sus consecuencias y otras instancias)',
  'Resumen completo, legible, con evidencias y veredictos: ' + ART + '/resumen.txt. Lo COMPILADO (en sondeos/ desde hoy):',
  '* L1-1: en el master VIEJO (2510f70, cons a b = pair a (σb)) `Prf ⊥` salía SIN hipótesis: prf_nil_or_cons 1 (Prf.listInd sin guarda) + Cantor (cons h t ≠ 1, allí cons 0 0 = 2). ADR-113 cierra ESA ruta (cons 0 0 = 1), sin probar la consistencia. sondeos/PrfBotCodificacionVieja.lean.',
  '* L1-2: ax_list_induction (Full/Lists.lean:79) sola da axioms ⊢ ⊥ (su φ : Term → Formula no es uniforme). sondeos/ListInductionAxiomRefutable.lean.',
  '* L1-3: los 22 constructores de Derives son sólidos para la valuación booleana POR INDUCCIÓN y sin axiomas; los enunciados de imp_intro, raa y ax_list_induction son FALSOS, y Lean + cualquiera de ellos ⊢ False. sondeos/MetaReglasRefutables.lean. 53 de 517 filas de check-footprints sin contenido.',
  '* L1-4: OmegaConsistent (Meta/OmegaReflect.lean:267) es refutable por su definición (testigos sólo StdChain). sondeos/OmegaConsistentRefutable.lean.',
  '* F1: [AnclaEq] (Meta/Representability2Prf.lean:122) implica Prf ⊥; tras ADR-113 es el obstáculo de Gödel I/II sobre Prf. sondeos/AnclaEqInconsistente.lean. Arreglo preferido (L2-3): axiomsCodeT sigue opaco y se añade UN axioma diagonal `axiomsCodeT = LR ++ [δ]` (selfAppN ψ) con diagTerm (Meta/Diagonal.lean:104) y prf_diag_arith_num (Meta/GodelTwoPrf.lean:116).',
  '',
  '## Decisiones del propietario del 2026-10-02 (son el marco; no las discutas, mídelas)',
  '1. ADR-113 fusionado (hecho). 2. La capa ⊢ se RETIRA como capa de trabajo: queda Prf, más un puente a Derives₀ si hace falta; las meta-reglas de FOL se RETIRAN («no hacemos uso de herramientas que no sean verdaderas»). 3. Esta ronda 2. 4. Las sondas, en sondeos/. Y pendiente: D7 (String → List Char en FOL) «en el momento óptimo».',
  '',
  '## Reglas (OBLIGATORIAS)',
  '* SÓLO LECTURA. No edites, no crees ni borres ficheros en ningún repositorio, no hagas commits ni cambies de rama. Herramientas: Read, Grep, Glob y git de sólo lectura.',
  '* ⛔ NO compiles: nada de lake, lake build, lake env lean ni lean. Si algo sólo se zanja compilando, dilo y escribe el texto de la sonda Lean que lo zanjaría.',
  '* Cada cifra va MEDIDA (di cómo) o etiquetada como ESTIMACIÓN.',
  '* Trampas de notación: dentro de RPP, ∧ ∨ ¬ ≤ ∈ ⇒ ⇔ suelen ser símbolos OBJETO; los de Lean son And/Or/Not.',
  '* Antes de afirmar que algo FALTA, búscalo.',
  '* Prioriza problemas de BASE y planes ejecutables con su radio medido.',
].join('\n')

const SALIDA = 'Rellena el esquema. En «examinado», lo que miraste de verdad; en «no_examinado», lo que tu lente debería cubrir y no cubriste. Cada hallazgo: afirmación FALSABLE, evidencia con fichero:línea y cita, cómo verificarlo (con sonda_lean si hace falta compilar), por qué frena, y relación con F1. Un «no hay» medido también es un resultado: dilo en el resumen.'

const LENSES = [
  {
    key: 'R2-1-consistencia',
    titulo: 'R2-1 · ¿Queda alguna refutación barata de ConsistentH en la base reparada?',
    encargo: 'Sobre master con ADR-113, busca otras derivaciones de Prf ⊥ o de ¬ConsistentH al estilo de L1-1: (a) cada teorema de Prf que sale de Prf.listInd o Prf.ind (ADR-090 censó 21 usos de listInd, 13 sin guarda), evaluado en numerales pequeños (0…3) con el consN nuevo; (b) cada regla de Prf (Meta/Hilbert.lean:100-250: Prfᵢ, p3, ind, qconf, listInd, gen, mp) frente al modelo estándar; (c) cada símbolo que la teoría sólo fija sobre formas canónicas (lineWF, premsOf, validProofFn sobre líneas no canónicas, carc/cdrc en nil, nthc fuera de rango, − con b > a): aplica el método de reemplazo de F1 y busca hipótesis o lemas que fijen su VALOR; (d) toda clase, DEUDA_* o hipótesis Prop de resultados titulares. Si no encuentras nada, mide qué falta para un modelo de los 141 (sondeos/ModeloNat.lean y la capa de listas) y si hay obstáculo de principio.',
  },
  {
    key: 'R2-2-retiro',
    titulo: 'R2-2 · Retirar la capa ⊢ y las meta-reglas: el radio y el orden',
    encargo: 'Haz el plan ejecutable de la decisión 2, con el radio MEDIDO: (a) las definiciones de la cadena Prf que viven en módulos ⊢ (Prf, Prfᵢ, inductionFormula, listInductionFormula, confinementFormula, provFormulaC\', provCodeC\', diagTerm, selfAppN, godelPred\'/godelBeta\', godelCN, consistencyFormula\', formCode, numeral…) y a dónde moverlas sin ciclo de imports; (b) todos los consumidores de FOL.MetaRules en FOL y en RPP (por import y por nombre), y qué se borra y qué se porta; (c) los 3 axiom de RPP sobre ⊢ y sus consumidores; (d) qué de la librería ⊢ (Minimal/Theorems, Full, Meta) usa la cadena Prf de verdad (por constante, no por footprint); (e) si hace falta el puente Prf ↔ Derives₀ (L4-4: la forma correcta es Prf φ ↔ DerivesSet₀ TPrf φ) y para qué resultados; (f) qué toca de PeanoRF (sólo lectura) y de los controles (check-footprints, check-axioms, check-estratos, check-doc-sync), y qué textos falsos hay que corregir. Propón el orden de commits con criterio de abandono.',
  },
  {
    key: 'R2-3-f1',
    titulo: 'R2-3 · El arreglo de F1 sobre la base reparada (el axioma diagonal de L2-3)',
    encargo: 'Diseña con detalle, contra el código actual, el arreglo L2-3: `ax_axiomsCodeT_def := selfAppN ψ` con ψ := (axiomsCodeT =eq concat LR (cons diagTerm nil)). Mide: (a) el ciclo de imports (codeNat, diagTerm, selfAppN viven en Meta/ y axioms en Minimal/): qué hay que bajar o duplicar; (b) TODA prueba que evalúa la lista axioms o sus elementos (rfl, decide, simp [axioms], findIdx, getD, axioms_eq, axioms_len, axioms_lift_eq en Meta/Hilbert.lean:64-71, filtro_occ del sondeo F1): cuáles expondrían el numeral gigante; (c) la posición del axioma nuevo (último) y los índices Rule.thy k, findIdx, decodeRuleTag; (d) si es verdadero en ℕ con la interpretación estándar de substfc y tcFn; (e) cómo se derivan después la instancia de AnclaEq, prf_inAxC, pcc_In_axiomsCodeT_tracked y la pertenencia NEGATIVA (necesaria para NegVerifier); (f) si retirar antes el bloque validProofFn (22 axiomas, ax_vpf_thy incluido; L5-05) lo simplifica; (g) la regla de diseño: ningún símbolo nuevo con ecuaciones a la vez sobre σ y sobre cons. Escribe el esqueleto Lean (sonda_lean) del teorema del ancla.',
  },
  {
    key: 'R2-4-fol',
    titulo: 'R2-4 · FOL como base de RPP tras la decisión 2',
    encargo: 'RPP está construido sobre FOL. Audita lo que RPP usará de FOL cuando deje la capa herramienta: la sintaxis genérica (TermG/FormulaG, subst, lift: FOL/FOL/FOL.lean), FOL/FOL/Semantics.lean (libre, lo usará la solidez de Prf), Derives₀/Derives₁, DerivesSet₀ (FOL/FOL/Henkin0.lean:122), soundness₀, completeness₀, model_existence_iff₀ (Compacity0). Busca: hipótesis vacuas o insatisfacibles en titulares de FOL; docstrings que afirman más que el lema (como el de Inconsistencia.lean); dependencias ocultas de MetaRules o de Derives en la capa ₀; qué necesita FOL para RETIRAR MetaRules (sus consumidores en FOL: Tactics, Deduction, Theorems.*, Inconsistencia, TheoryFramework; los textos de AXIOMS.md, REFERENCE.md, NEXT-STEPS.md); qué de eso toca módulos congelados (frozen_files.txt) o bloqueados (locked_files.txt); y cómo encaja D7 (String → List Char) en esa misma ventana (los 3 abbrev de FOL/FOL/FOL.lean:69-70 y Semantics.lean:32; 14 de los 23 congelados mencionan String).',
  },
  {
    key: 'R2-5-critico',
    titulo: 'R2-5 · Crítico de completitud: lo que ninguna lente ha mirado',
    encargo: 'Lee el resumen de la ronda 1 y su lista de omisiones, y busca problemas de base que ninguna lente examinó. Candidatos: la corrección de la codificación (inyectividad, decidibilidad, el puente árbol/numeral de CodeNumeralPrf); el punto fijo de G (godelCN, prf_godelCN_fixedpoint) y los enunciados de D1-D3 (¿dicen lo que la cadena necesita?); que la teoría de Gödel sea r.e. de verdad (M-10); otros `axiom`, `sorry`, `native_decide`, `implemented_by`, `opaque` en RPP, FOL y TheoryFramework; controles que pueden dar verde sin comprobar (por ejemplo, los check-*.bash frente al cambio de ubuntu-latest a Ubuntu 26 el 2026-10-19: ¿qué herramientas del runner usan?); y, tras las reparaciones previstas (ADR-113, retiro de ⊢, arreglo de F1), qué hipótesis abiertas quedarían en Gödel I y II y si son satisfacibles a la vez.',
  },
]

const VERIF = [
  'Te paso los hallazgos que otro auditor encontró con esta lente. Intenta REFUTAR cada uno:',
  '* comprueba que cada cita fichero:línea existe y dice lo que se afirma;',
  '* comprueba que la afirmación se sigue y que no está ya resuelta en el árbol (búscalo);',
  '* corrige la gravedad si está inflada o rebajada;',
  '* escéptico por defecto: si leyendo no puedes confirmarlo, el veredicto es «plausible» o «no_verificable_sin_compilar», nunca «confirmado»;',
  '* no compiles.',
  'Además, en «omisiones», lista lo que esta lente debería haber examinado y no examinó: alimenta la ronda 3.',
].join('\n')

const GRAVEDAD = ['bloqueante', 'grave', 'medio', 'menor']
const FINDINGS_SCHEMA = {
  type: 'object',
  properties: {
    lente: { type: 'string' },
    resumen: { type: 'string' },
    examinado: { type: 'array', items: { type: 'string' } },
    no_examinado: { type: 'array', items: { type: 'string' } },
    hallazgos: {
      type: 'array',
      items: {
        type: 'object',
        properties: {
          id: { type: 'string' },
          titulo: { type: 'string' },
          gravedad: { type: 'string', enum: GRAVEDAD },
          nivel: { type: 'string', enum: ['base', 'detalle'] },
          afirmacion: { type: 'string' },
          evidencia: { type: 'array', items: { type: 'string' } },
          medido_o_estimado: { type: 'string', enum: ['medido', 'estimado', 'mixto'] },
          por_que_frena: { type: 'string' },
          como_verificar: { type: 'string' },
          sonda_lean: { type: 'string' },
          arreglo_propuesto: { type: 'string' },
          relacion_con_F1: { type: 'string' },
          confianza: { type: 'string', enum: ['alta', 'media', 'baja'] },
        },
        required: ['id', 'titulo', 'gravedad', 'nivel', 'afirmacion', 'evidencia', 'medido_o_estimado', 'por_que_frena', 'como_verificar', 'confianza'],
      },
    },
  },
  required: ['lente', 'resumen', 'examinado', 'no_examinado', 'hallazgos'],
}
const VERDICT_SCHEMA = {
  type: 'object',
  properties: {
    veredictos: {
      type: 'array',
      items: {
        type: 'object',
        properties: {
          id: { type: 'string' },
          veredicto: { type: 'string', enum: ['confirmado', 'plausible', 'refutado', 'no_verificable_sin_compilar'] },
          razon: { type: 'string' },
          evidencia_contraria: { type: 'array', items: { type: 'string' } },
          gravedad_corregida: { type: 'string', enum: GRAVEDAD },
          necesita_compilacion: { type: 'boolean' },
        },
        required: ['id', 'veredicto', 'razon', 'necesita_compilacion'],
      },
    },
    omisiones: { type: 'array', items: { type: 'string' } },
  },
  required: ['veredictos', 'omisiones'],
}

log('Ronda 2: cinco lentes sobre la base reparada, cada una con su verificador adversarial')
const results = await pipeline(
  LENSES,
  l => agent(CONTEXTO + '\n\n# TU LENTE: ' + l.titulo + '\n\n' + l.encargo + '\n\n' + SALIDA,
    { label: 'audit:' + l.key, phase: 'Auditoría', schema: FINDINGS_SCHEMA }),
  (found, l) => found
    ? agent(CONTEXTO + '\n\n# VERIFICADOR ADVERSARIAL — ' + l.titulo + '\n\n' + VERIF + '\n\nHallazgos a verificar (JSON):\n' + JSON.stringify(found, null, 1),
        { label: 'verif:' + l.key, phase: 'Verificación', schema: VERDICT_SCHEMA })
        .then(v => ({ lente: l.key, auditoria: found, verificacion: v }))
    : null,
)
const ok = results.filter(Boolean)
const n = ok.reduce((s, r) => s + ((r.auditoria && r.auditoria.hallazgos) ? r.auditoria.hallazgos.length : 0), 0)
log(ok.length + '/' + LENSES.length + ' lentes completas; ' + n + ' hallazgos antes de verificar')
return ok

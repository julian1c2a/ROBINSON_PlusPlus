# Frente Gödel — Nivel D real: aritmetización de D1–D3

**Created:** 2026-06-13 · **Author:** Julián Calderón Almendros
**Status (2026-06-24):** 🟢 muy avanzado — **Gödel I real + D1 real (⊢ y finitaria `Prf`) + D2 real ⊢ COMPLETOS**; **teorema de deducción finitario** y **regla de confinamiento ∀ `qconf`** integrados; **fix de solidez FOL** (axioma De Bruijn falso → teorema). **En curso:** Gödel II finitario (`goedel_second_prf : ConsistentH → ¬ Prf Con'`) — bloqueado en el **lema de Barendregt** (composición subst–subst niveles mixtos) → inducción de listas en `Prf` (`Prf.listInd`) → `d2_prf`/`d3_prf`. 47 módulos, 60 jobs, 0 sorrys. (El plan por fases de abajo es la hoja de ruta original; ver [NEXT-STEPS.md](NEXT-STEPS.md)/[CHANGELOG.md](CHANGELOG.md) para el detalle vivo.)
**Decisión:** Opción **A** (aritmetización real) — ver §0.

Este documento especifica el plan para convertir las condiciones de
demostrabilidad de Hilbert-Bernays-Löb **D1, D2, D3** de *meta-axiomas* (estado
2026-06-13) en **teoremas**, sobre un sistema finitario nuevo.

---

## 0 · Por qué hace falta un sistema nuevo (el muro de la ω-regla)

El sistema de demostrabilidad actual del proyecto, `axioms ⊢ φ` (`Derives` +
meta-reglas de `FOL/MetaRules.lean`), incluye la **ω-regla** `gen`:

```text
gen : (∀ n : Term, Γ ⊢ A[n]) → Γ ⊢ ∀A      -- premisas INFINITAS
```

El propio módulo lo declara: el sistema es *"sólido y completo relativo a ℕ"* —
es **ω-lógica**. Consecuencias que **bloquean** D1–D3 como teoremas sobre `⊢`:

1. **`⊢` no es r.e.** Captura la verdad en ℕ. Una demostración con la ω-regla
   tiene infinitas premisas ⟹ no hay código de prueba finito ⟹ el predicado de
   prueba `Dem d x` no puede ser primitivo recursivo ⟹ `provFormula` no puede
   ser una fórmula Σ₁ honesta.
2. **Tarski.** El `provFormula_repr` bicondicional actual dice
   `⊢ Prov(⌜φ⌝) ↔ ⊢ φ`, i.e. `Prov` rastrea la verdad en ℕ; por la
   indefinibilidad de la verdad **ninguna `Formula` la define**. Un `provFormula`
   concreto que satisfaga ese bicondicional *no puede existir*.

**Por tanto** Gödel se aplica a un **sistema finitario `⊢ᴴ` nuevo, en paralelo**.
El ω-`⊢` se conserva intacto (da la solidez/completitud relativa a ℕ y soporta
todo lo ya hecho: Full, TFA, Gödel I/II vía postulados). El finitario es lo que
se aritmetiza.

Buena noticia: el núcleo `Derives` (constructores `intro_impl`, `elim_*`,
`intro_forall`, …) **ya es finitario y r.e.**; sólo las meta-axiomas ω apiladas
encima lo vuelven ω-lógico. Usaremos `Derives` (+ las ω-reglas, lícitas aquí
porque sólo van *hacia* el sistema fuerte) como **destino del puente de
solidez**.

---

## 1 · Decisiones de diseño (ADR)

| # | Decisión | Elección | Razón |
|---|---|---|---|
| D-1 | Sistema finitario objetivo | **Cálculo de Hilbert fresco** `⊢ᴴ` | Lo más limpio de codificar (una prueba es una lista de fórmulas); estándar en la literatura (O'Connor/Coq, Paulson/Isabelle). |
| D-2 | Relación con el sistema existente | **Paralelo, no reemplazo** | Tocar la ω-regla destruiría Full/TFA/Gödel I-II. Nuevos módulos `Meta/Hilbert*.lean`. |
| D-3 | Codificación de secuencias | **Listas `cons`/`nil`** (de `Meta/Godel.lean`) | Ya inyectivas y probadas; más simple que la primorial/TFA. |
| D-4 | Fuerza del sistema | **Q (= axiomas de Minimal) para Gödel I**; **+ esquema de inducción** sólo al llegar a D3 | Q basta para Gödel I (Fases 0–3). D3 (Σ₁-completitud *provable*) necesita ~IΣ₁; la inducción se añade como **esquema finitario de axiomas** (no ω-regla) en la Fase 5. |
| D-5 | Forma del sistema en Fase 0 | **`Prf : Formula → Prop` inductivo** | El puente de solidez sale por inducción estructural trivial. La forma "secuencia + `IsProof` decidible" (necesaria para codificar) se introduce en Fase 1 con la equivalencia `Prf ↔ ∃ seq`. |

---

## 2 · El cálculo de Hilbert `⊢ᴴ` (Fase 0) — especificación

Lenguaje: el de `FOL.FOL` (De Bruijn; `⊥, atom, ≐, ⇒, ∀, ∧, ∨, ∃` primitivos).
`¬A := A ⇒ ⊥`. Clásico (esquema P3 = DNE), coherente con el `dne` del ω-sistema.

**Esquemas de axiomas** (para todas las `Formula` A,B,C y `Term` t):

```text
Proposicionales
  P1   A ⇒ (B ⇒ A)
  P2   (A ⇒ (B ⇒ C)) ⇒ ((A ⇒ B) ⇒ (A ⇒ C))
  P3   ((A ⇒ ⊥) ⇒ ⊥) ⇒ A                       (DNE clásica)
Conjunción
  C1   A ⇒ (B ⇒ (A ∧ B))
  C2   (A ∧ B) ⇒ A
  C3   (A ∧ B) ⇒ B
Disyunción
  J1   A ⇒ (A ∨ B)
  J2   B ⇒ (A ∨ B)
  J3   (A ⇒ C) ⇒ ((B ⇒ C) ⇒ ((A ∨ B) ⇒ C))
Falsum
  EFQ  ⊥ ⇒ A
Cuantificadores (De Bruijn; substFormula 0 t / liftFormula 0)
  Q1   (∀A) ⇒ A[t/0]                             (∀-elim / instanciación)
  Q2   A[t/0] ⇒ (∃A)                             (∃-intro)
  Q3   (∀(A ⇒ ↑B)) ⇒ ((∃A) ⇒ B)                  (∃-elim; ↑B = liftFormula 0 B
                                                  codifica "0 ∉ libre(B)")
Igualdad
  E1   t ≐ t                                     (refl)
  E2   (t₁ ≐ t₂) ⇒ (A[t₁/0] ⇒ A[t₂/0])           (Leibniz)
Teoría
  THY  a            para cada a ∈ Minimal.axioms
```

**Reglas:**

```text
MP    de ⊢ᴴ (A ⇒ B) y ⊢ᴴ A   concluye ⊢ᴴ B
GEN   de ⊢ᴴ A                concluye ⊢ᴴ (∀A)
```

`GEN` sin restricción es sólido porque las pruebas parten sólo de axiomas
(cerrados): es el modo-teorema estándar de Hilbert. El esquema de inducción
(Fase 5) se añadirá como familia `IND a`.

**Definición:** `ProvableH φ := Prf φ`. (Fase 1: `↔ ∃ seq, IsProof seq ∧ last = φ`.)

---

## 3 · Resultados de la Fase 0  ✅

Implementado en `Meta/Hilbert.lean` (build verde, 40 jobs, 0 sorry, **0 axiomas
nuevos** — `Prf₀`/`Prf` son *definiciones* inductivas, los puentes son
*teoremas*). El sistema se factoriza en **dos capas** para exhibir la clasicidad:

1. **`Prf₀` (intuicionista)** — todos los esquemas salvo DNE, + MP + GEN.
   Puente **`prf0_to_derives : Prf₀ φ → axioms ⊢ φ`** construido con **solo
   constructores de `Derives`** (reusando los teoremas constructor-puros de
   `FOL.Theorems`).
2. **`Prf` (clásico)** — `incl (Prf₀)` + esquema DNE (`p3`) + MP + GEN.
   Puente **`prf_to_derives : Prf φ → axioms ⊢ φ`** que reusa el intuicionista y
   emplea **`dne` en un único punto** (caso `p3`).

**Verificación mecánica de dónde entra lo clásico** (`#print axioms`):

```text
prf0_to_derives  depends on: [propext, Quot.sound, subst_lift_cancel_formula]
prf_to_derives   depends on: [propext, Quot.sound, FOL.MetaRules.dne,
                              subst_lift_cancel_formula]
```

La diferencia es **exactamente `{FOL.MetaRules.dne}`**. `subst_lift_cancel_formula`
es un axioma De Bruijn computacional (mecánica de sustitución, **ortogonal a la
lógica**), usado solo en el esquema de ∃-elim `q3`. Conclusión formal:

> **Nuestro FOL (los constructores nativos de `Derives`) deriva todo el cálculo
> de Hilbert; el único ingrediente no constructivo es una aplicación de DNE
> clásica, y la ω-regla no se invoca jamás** (GEN de Hilbert = `intro_forall`,
> finitaria de una premisa).

Esto da además la **consistencia transferida** `consistentH_of_omega :
ConsistentOmega → ConsistentH`: la hipótesis de Gödel sobre `⊢ᴴ` se hereda de la
del sistema fuerte.

(El recíproco `axioms ⊢ φ → Prf φ` es **falso** —y debe serlo—: el ω-sistema
prueba estrictamente más, p. ej. inducción object-level. Justo por eso `⊢ᴴ` es
incompleto y Gödel aplica.)

---

## 4 · Roadmap de fases

| Fase | Entrega | Estado |
|---|---|---|
| **0** | `Meta/Hilbert.lean`: `Prf₀`/`Prf` + puentes `prf0_to_derives`/`prf_to_derives` + consistencia transferida | ✅ |
| **1a/b** | `Meta/HilbertSeq.lean`: `Rule`, verificador decidible `checkProof`, `Derivation`, **solidez + completitud** ⟹ `Prf φ ↔ ∃ rs, Derivation rs φ` | ✅ |
| **1c** | `Meta/HilbertSeq.lean` (cont.): coding `ruleCode`/`rulesCode` → `Term`, `Dem` **concreto** + `dem_tracks : (∃ d, Dem d ⌜φ⌝) ↔ Prf φ` (solo axiomas estándar de Lean) | ✅ |
| **2** | Aritmetización (CodeArith/SubstArith/StepArith/CheckArith/Representability): sustitución y lift De Bruijn como funciones object, verificador `validProofFn`, `provFormulaC` Σ₁, **representabilidad positiva** `repr_pos`. Desglose y estado fino en **§7**. | ✅ (2.1–2.5 ✅; 2.6 negativa diferida) |
| **3** | **D1** real (`Meta/Necessitation.lean`): `d1/necessitation : Prf φ → axioms ⊢ provCodeC φ` (= `repr_pos`) + Gödel I modular `goedel_first_unprovable_real` | ✅ |
| **3.5** | **Lema diagonal real** (`Meta/Diagonal.lean`): `tc_arith` + `diag_arith` + `godelC_fixedpoint : ⊢ G ⇔ ¬provCodeC G` ⟹ **`goedel_first_real : ConsistentOmega → ¬ Prf G`** — **Gödel I real SIN hipótesis ni postulados** (`#print axioms` = solo `imp_intro`/`dne`/`subst_lift_cancel_formula` del ω-sistema, ningún `diagonal_lemma`/`provFormula`/D2/D3) | ✅ |
| **4** | **D2** real: combinador MP sobre códigos + internalización | ⬜ |
| **5** | **D3** real: + esquema de inducción `IND`; Σ₁-completitud *provable* | ⬜ |

Fases 0–3 ⟹ **Gödel I sin postulados**. Fases 4–5 ⟹ Gödel II/Löb sin postulados.
**Compromiso por tramos:** cerrar 0–1 y reevaluar antes de la bestia (D3).

---

## 5 · Qué reemplaza a qué (al final)

| Postulado actual | Pasa a | Fase |
|---|---|---|
| `Dem : Term → Term → Prop` (axiom, opaco) | def concreta (decodificador) | 1 |
| `dem_iff_provable` (axiom) | teorema (equivalencia secuencia) | 1 |
| `provFormula : Formula` (axiom, opaco) | def concreta Σ₁ | 2 |
| `provFormula_repr` bicondicional (axiom) | **sólo necesitación** (la reflexión muere por Tarski) | 3 |
| `D2`, `D3` (axiom) | teoremas | 4, 5 |
| `diagonal_lemma` (axiom) | **✅ teorema** (`Meta/Diagonal.lean`): `tc_arith`/`tc_form` «código del código» + `diag_arith` + **`godelC_fixedpoint : ⊢ G ⇔ ¬provCodeC G`** (punto fijo real). El paso de composición De Bruijn se resuelve para el `φ` concreto vía `substTerm_lift_comm` | 4 ✅ |

---

## 7 · Fase 2 — descomposición (aritmetización total, Opción A)

Decisión 2026-06-13: **aritmetización total** — `demFormula` será una `Formula`
Σ₁ concreta que internaliza `checkProof`, con `Dem d x → ⊢ᴴ demFormula[⌜d⌝,⌜x⌝]`
demostrada (no postulada). Es el mayor bloque del proyecto; se construye por
sub-pasos verificados.

**Observación que acota el esfuerzo de D1:** para la **necesitación** (Fase 3,
D1) basta la dirección **positiva** `Dem d x → ⊢ᴴ demFormula[⌜d⌝,⌜x⌝]`. En una
demostración válida concreta todas las comparaciones de igualdad del verificador
**aciertan**, luego se resuelven por reflexividad/aritmética de numerales; la
**distinción** de códigos (dirección negativa) sólo hace falta para la reflexión
(Gödel I-soundness / parte de D3), y se difiere.

**Motor (patrón `Full.Numerals`):** la **inducción meta** (en Lean) demuestra
hechos de **cómputo object-level**; `⊢ᴴ` no necesita inducción, sólo las
ecuaciones recursivas de cada función object. Cada operación del coding se
axiomatiza como función object (símbolo + ecuaciones, estilo `pow`/`prod_pairs`)
y su corrección sobre entradas concretas se prueba por inducción meta.

| Sub-paso | Contenido | Estado |
|---|---|---|
| **2.1** | `Meta/CodeArith.lean`: puente `numeral_bridge`, separación `gnum_ne`, orden `gnum_lt`, homomorfismos `gnum_add/mul`, reflexividad `gnum_refl` | ✅ |
| **2.2t** | `Meta/SubstArith.lean` (nivel **término**): funciones object `substtc`/`substtsc` + ecuaciones recursivas **integradas en `Minimal.axioms`** (re-derivadas como teoremas vía `ax`+`spec`; `substTerm_arith` depende solo de axiomas estándar de Lean) + congruencias de `cons` + `substTerm_arith`/`substTerms_arith` por inducción meta mutua. Lema auxiliar `substTerm_liftLiftLift` (triple lift, para `forall_4`) | ✅ |
| **2.2f** | nivel **fórmula** (`Meta/SubstArith.lean` + `Minimal/Axioms.lean`): `liftc`/`liftsc` (lift aritmetizado) + `substfc` (8 constructores de código `botc`..`exc`) + 13 ecuaciones recursivas **en `Minimal.axioms`** (re-derivadas como teoremas) + `liftTerm_arith` + `substFormula_arith` (binders ∀/∃ con `succ`-nivel y `liftc zero`-substituyendo). `substFormula_arith` depende solo de axiomas estándar de Lean | ✅ |
| **2.3** | `Meta/StepArith.lean`: reconocimiento de instancias de axioma — `q1/q2/leibniz_concl_code` (esquemas de sustitución, vía `substFormula_arith`); los proposicionales son definicionales (refl); MP/Gen van con la secuencia (2.4) | ✅ |
| **2.4-c** | `Meta/CheckArith.lean` (cimientos): `numeralM` (`= Godel.numeral`), extractores `carc`/`cdrc` + cómputo | ✅ |
| **2.4-v** | verificador `validProofFn` + `forall_5` + **17 ecuaciones** en `Minimal.axioms` (params directos por binders, etiqueta de regla embebida; MP/Gen condicionales por `In`); `substTerm_liftLiftLiftLift` (4-lift); 17 step lemmas `vpf_*`; **`provFormulaC := ∃p, In x (validProofFn nil p)`** (Σ₁) + `provCodeC` | ✅ |
| **2.4-thy** | regla `thy`: la línea **transporta el código** del axioma (no su índice); `ruleCode (.thy k)` emite `formCode (coreAxioms[k])`. Verificador **completo: 18 reglas** | ✅ |
| **thy-sound** | **solidez de `thy`** (predicado fiel): `formCodeM` a nivel `Minimal` + teoría `coreAxioms` (34 axiomas matemáticos, sin las ecuaciones de coding) + `axiomsCodeT` (código object, **opaco** → sin ciclo: `axiomsCodeT ∌ formCode(ax_vpf_thy)`) anclado por `ax_axiomsCodeT`. `ax_vpf_thy` pasa a **condicional** `In c axiomsCodeT ⇒ …`; `Prf₀.thy`/`stepConcl` recorren `coreAxioms`. Clausura De Bruijn `liftTerm_formCodeM` (los códigos tienen numerales gigantes de símbolos Unicode ⟹ `axioms_lift_eq` se prueba estructuralmente, no por `rfl`). Puente `formCodeM = formCode`. **`provCodeC` ya no es trivialmente ⊤** | ✅ |
| **2.5** | **Representabilidad positiva** ✅ `Meta/Representability.lean`: `repr_pos : Prf φ → axioms ⊢ provCodeC φ`. Encoder object **a medida** `proofCode`/`lineCode` (las líneas `mp`/`gen`/`thy` transportan códigos de fórmulas resueltos, alineado con `validProofFn`; el `ruleCode` de 1c era por índices). Inducción de seguimiento `vpf_run` (18 casos; Q1/Q2/Q3/Leibniz vía `*_concl_code` + `liftFormula_arith`; MP/Gen descargan la pertenencia con `In_listFormCode`). Ensamblaje por `intro_ex` (el lift de `provFormulaC` se cancela con la sustitución del testigo, sin necesitar clausura de `formCode`). `#print axioms repr_pos` = solo `propext/Classical.choice/Quot.sound` | ✅ |
| **2.6** | representabilidad **negativa** `¬Dem d x → ⊢ᴴ ¬provCodeC φ` (reflexión/D3). **Aritmética negativa de códigos ✅** (`Meta/CodeDistinct.lean`): `formCode_ne : A≠B → ⊢ ¬(⌜A⌝=⌜B⌝)` + familia `termCode_ne`/`strCode_ne`/`charsCode_ne` + primitivos `cons_ne_head/tail`/`neg_symm`. El resultado titular `⊢ ¬provCodeC φ` es **Π₁** y necesita el **esquema de inducción (Fase 5)** | 🟡 (aritmética negativa ✅; falta inducción) |

> Honestidad de scope: 2.2 (aritmetización de la sustitución De Bruijn) es el
> núcleo duro; requiere extender el lenguaje object con funciones de coding y sus
> axiomas recursivos. Es trabajo de varias sesiones.

## 6 · Referencias

- O'Connor, R. (2005). *Essential Incompleteness of Arithmetic Verified by Coq.*
- Paulson, L. (2014). *A Machine-Assisted Proof of Gödel's Incompleteness Theorems for the Theory of Hereditarily Finite Sets.*
- Boolos–Burgess–Jeffrey, *Computability and Logic*, cap. 17–18.
- Documento hermano: [GODEL-STATUS.md](GODEL-STATUS.md).

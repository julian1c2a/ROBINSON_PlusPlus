/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.CheckArith

import FOL.FOL
import FOL.Theorems.Eq
import FOL.Deduction
import FOL.Tactics
import FOL.Theorems.Derived
import FOL.Theorems.Impl
import FOL.Theorems.Neg
import FOL.Theorems.Quantifiers
import ROBINSON_PlusPlus.Full.Induction
import ROBINSON_PlusPlus.Minimal.Axioms

/-!
> 🗑️ **2026‑10‑02 · ADR‑115 — leer antes que el resto.** La capa `⊢` se retiró de RPP, y con ella todo lo
> que este módulo tenía sobre `⊢`. Los nombres de esa capa que cite el texto de abajo
> (`repr_pos`, `ax_list_induction`, `In_mono_right`, `prf_to_derives`) **ya no existen**: lo que se lea sobre ellos es REGISTRO, no estado.
> Lo que queda en el módulo no depende de `⊢`.
-/

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.SubstArith
open ROBINSON_PlusPlus.Meta.CheckArith

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Meta.ProofChain

/-!
## META — NIVEL D real: verificador estructural `runFn` (Fase R1)

Hacia **D2/D3 → Gödel II real**. La `validProofFn` (CheckArith) tiene ecuaciones
**condicionales** y opacas: solo reduce sobre códigos de prueba concretos, lo que
basta para la dirección positiva (`repr_pos`, Gödel I real) pero **bloquea** el
razonamiento object-level sobre testigos de prueba ARBITRARIOS que D2/D3 exigen.

`runFn` lo resuelve: cada línea lleva su conclusión incorporada como cabeza
(`line = cons ⌜concl⌝ justif`), así `runFn c (cons line rest) = runFn (c ++ [carc
line]) rest` reduce **uniformemente** vía `carc`, sin depender de la regla. Eso
habilita la **inducción estructural object-level**: sobre `⊢` era `Full.ax_list_induction`,
retirado (ADR‑115); en `Prf` es el constructor `Prf.listInd` (`prf_list_induction`,
`Meta/ChainPrf.lean`).

Esta fase establecía los **fundamentos**: ecuaciones de `runFn`, congruencias, y la
**compositividad** `runFn c (p ++ s) =eq runFn (runFn c p) s` (lema angular de
D2/D3). El acumulador `c` se generaliza como **∀ object** dentro de la propiedad
inductiva (los `liftTerm 0` se cancelan con la sustitución del testigo de `gen`).

🗑️ **2026‑10‑02 (ADR‑115) — registro.** Todos esos lemas eran de `⊢` y quedaron retirados con esa
capa, también el empaquetado de `provCodeC'` y la monotonía. Aquí quedan las definiciones: las
propiedades inductivas `compProp`, `weakProp`, `compChainProp` y `monoChainProp` (hoy sin
consumidor) y `provFormulaC'`/`provCodeC'`. Sus versiones `Prf` están en `Meta/ReprPrf.lean`
(ecuaciones y congruencias de `runFn`, `concat`, `In`, `allIn`/`chainOk`), `Meta/ChainPrf.lean`
(`prf_runFn_concat`, `prf_runFn_weaken`, `prf_chainOk_concat`, monotonía; con sus propios
predicados `prfCompPred`, `prfWeakPred`…) y `Meta/Representability2Prf.lean` (`provCodeC'_intro_prf`).
-/

/-! ### Compositividad de `runFn` (inducción estructural, acumulador ∀ object) -/

/-- Propiedad inductiva: `∀c. runFn c (p ++ s) =eq runFn (runFn c p) s`, con el
    acumulador `c` como `∀` object (`.var 0`) para que la HI aplique al contexto
    cambiado en el paso. `p`, `s` van `liftTerm 0` bajo el binder. -/
def compProp (s p : Term) : Formula :=
  Formula.forall
    (Formula.eq (runFn (.var 0) (concat (liftTerm 0 p) (liftTerm 0 s)))
                (runFn (runFn (.var 0) (liftTerm 0 p)) (liftTerm 0 s)))


/-! ### R3 — Debilitamiento de `runFn` -/

/-- Propiedad inductiva del debilitamiento: `∀c. runFn c p =eq c ++ runFn nil p`. -/
def weakProp (p : Term) : Formula :=
  Formula.forall
    (Formula.eq (runFn (.var 0) (liftTerm 0 p)) (concat (.var 0) (runFn nil (liftTerm 0 p))))


/-! ### R3 — Composición y monotonía de `chainOk` -/


/-- Propiedad inductiva de la composición de `chainOk`. -/
def compChainProp (s p : Term) : Formula :=
  Formula.forall
    ((chainOk (.var 0) (concat (liftTerm 0 p) (liftTerm 0 s))) ⇔
      land (chainOk (.var 0) (liftTerm 0 p)) (chainOk (runFn (.var 0) (liftTerm 0 p)) (liftTerm 0 s)))


/-- Propiedad inductiva de la monotonía de `chainOk`. -/
def monoChainProp (c0 p : Term) : Formula :=
  Formula.forall
    (Formula.impl (chainOk (.var 0) (liftTerm 0 p))
                  (chainOk (concat (liftTerm 0 c0) (.var 0)) (liftTerm 0 p)))


/-! ### R4 — predicado de demostrabilidad nuevo `provCodeC'` + validez de reglas -/

/-- **Predicado de demostrabilidad object (estructural)** Σ₁:
    `∃p, chainOk nil p ∧ In x (runFn nil p)` — "existe una cadena de prueba válida
    `p` cuyas conclusiones contienen `x`". Reemplaza `provFormulaC` (validProofFn)
    por el verificador estructural, apto para D2/D3. -/
def provFormulaC' : Formula :=
  Formula.ex (land (chainOk nil (.var 0)) (In (.var 1) (runFn nil (.var 0))))

/-- `Prov'(⌜φ⌝)` estructural. -/
noncomputable def provCodeC' (φ : Formula) : Formula := substFormula 0 (formCode φ) provFormulaC'

/-! ### 🗑️ Registro — los 21 esquemas `lineWF`/`premsOf` a nivel `⊢`

Estuvieron aquí, **probados por segunda vez desde los mismos axiomas** que sus gemelos `prf_*` de
`Meta/ReprPrf.lean`; luego se movieron a `Meta/LineWFDerives.lean`, como mero transporte por
`prf_to_derives`. Ese módulo y `prf_to_derives` quedaron retirados con la capa `⊢` (ADR‑115): los
esquemas viven sólo como los gemelos `prf_*` de `Meta/ReprPrf.lean`. -/

end ROBINSON_PlusPlus.Meta.ProofChain

export ROBINSON_PlusPlus.Meta.ProofChain (
  provFormulaC'
  provCodeC'
)

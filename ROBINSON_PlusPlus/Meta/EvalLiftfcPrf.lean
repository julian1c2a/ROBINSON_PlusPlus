import ROBINSON_PlusPlus.Meta.EvalSubstfcPrf
import ROBINSON_PlusPlus.Meta.EvalLiftcPrf
/-!
# `Meta/EvalLiftfcPrf.lean` — `pcc_eval_liftfc`: la base, y la deuda MEDIDA

`pcc_eval_liftfc` es lo único que separa a C3 del cierre: bloquea **4 de los 7** reflectores de
sustitución (q3 · 11, qconf · 19, ind · 18, listInd · 20), que son exactamente los que llevan
`liftfc` (§3.47.1). Este módulo pone la **base** y deja la obligación **enunciada, no
postulada** — idioma de `Meta/Sigma1BoundedPrf.lean` y `Meta/LineWFGuardPrf.lean`.

## Lo que la medición encontró, y que reclasifica una tarea

⚠️⚠️ **`pcc_eval_liftc` sólo vale a nivel `zero`.**

    pcc_eval_liftc (w s) (h : isTC1 w s) :
      Prf (provFromCode (eqc (liftcT (termCode zero) ṡ) ((liftc zero s)˙)))

(`Meta/EvalLiftcPrf.lean`, B2 · el DESCENSO). Y los axiomas `ax_liftfc_forall` / `ax_liftfc_ex`
**suben el nivel**:

    liftfc c (forallc a) = forallc (liftfc (σc) a)
    liftfc c (exc a)     = exc     (liftfc (σc) a)

⇒ una inducción sobre el código de fórmula **no puede quedarse en el nivel 0**: el predicado
tiene que cuantificar el nivel, y los casos `atom`/`eq` bajan a `liftsc`/`liftc` **a ese nivel**.

🔑 **Por tanto A5 —«generalizar más allá del nivel `zero`»— no es una mejora opcional: es
PRERREQUISITO de `pcc_eval_liftfc`, y por tanto de los cuatro tags que faltan.** Estaba
catalogada como generalización suelta; está en la ruta crítica.

## Lo que sí está, medido

* ✅ **Las ocho ecuaciones objeto** ya existen y son **genéricas en el nivel**:
  `prf_liftfc_bottom/atom/eq/impl/forall/and/or/ex` (`Meta/ArithPrf.lean:386-442`).
* ✅ La maquinaria de inducción fuerte es **genérica en `Φ`** (`prf_strong_induction`,
  `psi_lift_form1/2/3`, `PSI_inst*`, `Meta/StrongInductionPrf.lean`).
* ✅ El chasis de B3.4 (`pcc_eval_substfc_modulo_8`) es el **molde**: predicado + gate +
  instanciación de binders + un paso de 41 líneas que delega en ocho `Caso*`.
  ⚠️ **No es reutilizable tal cual**: sus `Caso*` están escritos sobre `targetSubstfc v s X`.
  Hacerlo genérico en el operador obligaría a refactorizar en vivo un módulo de 1 625 líneas
  que está en la ruta crítica de todo lo demás — se mide antes de tocarlo.
* ❌ `liftfcT` **no existía**: la imagen dotada de `liftfc`. Entra aquí, y **como DEFINICIÓN**
  (⛔ postular su ecuación de recursión como axioma OBJETO hace la teoría INCONSISTENTE — es la
  regla que ADR‑015/020 fijaron para `substfcT`).
-/

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.Hilbert ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.Sigma1Prf ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
open ROBINSON_PlusPlus.Meta.EvalArithPrf ROBINSON_PlusPlus.Meta.LiftcCodePrf
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs ROBINSON_PlusPlus.Meta.SubstfcWitnessPrf
open ROBINSON_PlusPlus.Meta.TrackedCorePrf ROBINSON_PlusPlus.Meta.EvalLiftcPrf
open ROBINSON_PlusPlus.Meta.DerivCondPrf ROBINSON_PlusPlus.Meta.CodeWitnessPrf.ENS

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Meta.EvalLiftfcPrf

/-! ## §1 · LA IMAGEN DOTADA DE `liftfc`, Y EL OBJETIVO

⛔ `liftfcT` entra como **definición**, igual que `substfcT` (`Meta/EvalArithPrf.lean:184`) y
`liftcT` (`Meta/LiftcCodePrf.lean:111`). Nunca como axioma. -/

/-- `⌜liftfc c f⌝` como constructor de código. -/
def liftfcT (c f : Term) : Term := funcc (strCode "liftfc") (cons c (cons f nil))

/-- El puente definicional con `termCode`: es lo que `formCode` produce de un `liftfc`. -/
theorem liftfcT_termCode (c f : Term) :
    liftfcT (termCode c) (termCode f) = termCode (liftfc c f) := rfl

/-- El código de la ecuación que hay que probar dentro de `Prov`. -/
def evalLiftfcCode (v X : Term) : Term :=
  eqc (liftfcT (tcFn v) (tcFn X)) (tcFn (liftfc v X))

/-- **EL OBJETIVO**: la evaluación provable de `liftfc`, con `v` y `X` abstractos. -/
def targetLiftfc (v X : Term) : Formula := provFromCode (evalLiftfcCode v X)

/-! ### Naturalidad (la piden el predicado de la inducción y su gate) -/

theorem liftTerm_evalLiftfcCode (k : Nat) (v X : Term) :
    liftTerm k (evalLiftfcCode v X)
      = evalLiftfcCode (liftTerm k v) (liftTerm k X) := by
  simp only [evalLiftfcCode, liftfcT, eqc, funcc, tcFn, liftfc, cons, nil, zero, succ,
    liftTerm, liftTerms, liftTerm_strCode]

theorem substTerm_evalLiftfcCode (k : Nat) (u v X : Term) :
    substTerm k u (evalLiftfcCode v X)
      = evalLiftfcCode (substTerm k u v) (substTerm k u X) := by
  simp only [evalLiftfcCode, liftfcT, eqc, funcc, tcFn, liftfc, cons, nil, zero, succ,
    substTerm, substTerms, substTerm_strCode]

theorem liftF_targetLiftfc (k : Nat) (v X : Term) :
    liftFormula k (targetLiftfc v X) = targetLiftfc (liftTerm k v) (liftTerm k X) := by
  simp only [targetLiftfc, liftFormula_provFromCode_open, liftTerm_evalLiftfcCode]

theorem substF_targetLiftfc (k : Nat) (u v X : Term) :
    substFormula k u (targetLiftfc v X) = targetLiftfc (substTerm k u v) (substTerm k u X) := by
  simp only [targetLiftfc, substFormula_provFromCode_open, substTerm_evalLiftfcCode]

/-! ### CONTROLES NEGATIVOS: el enunciado no es una reflexividad disfrazada

Mismo control que `Meta/EvalLiftcPrf.lean` pone sobre `liftcT`/`liftscT`. Sin él, un objetivo
como éste puede ser cierto por `rfl` y no decir nada. -/

example (v X : Term) : True := by
  fail_if_success
    exact (rfl : liftfcT (tcFn v) (tcFn X) = tcFn (liftfc v X))
  trivial

/-- Y el control POSITIVO de que la imagen es la buena: `liftfcT` **es** lo que `formCode`
    produce de un `liftfc` (ya está arriba como `liftfcT_termCode`, aquí sobre un caso real). -/
example (X : Term) :
    termCode (liftfc zero X) = liftfcT (termCode zero) (termCode X) := rfl

/-! ## §2 · LA DEUDA, ENUNCIADA (cero `axiom`)

Idioma de `Meta/LineWFGuardPrf.lean`: se enuncia, no se postula. -/

/-- **La obligación**: `liftfc` evaluado dentro de `Prov`, con el nivel `v` y el código `X`
    **abstractos**, bajo la guarda de buena formación de ADR‑020.

    ⚠️ Nótese que la guarda es **sólo** `hasWitF X`: `liftfc` no tiene sustituyendo, así que no
    hay `hasWit s` que arrastrar. Es más barata que la de `substfc` en ese punto. -/
abbrev DEUDA_evalLiftfc : Prop :=
  ∀ v X : Term, Prf (Formula.impl (hasWitF X) (targetLiftfc v X))

/-- La forma **guardada por el testigo explícito**, que es la que la inducción produce
    (espeja `pcc_eval_substfc`, cuyo antecedente es `isFC1 wF wT f`). -/
abbrev DEUDA_evalLiftfc_isFC1 : Prop :=
  ∀ wF wT v X : Term, Prf (Formula.impl (isFC1 wF wT X) (targetLiftfc v X))

/-- Y el puente entre las dos: el `∃∃` de `hasWitF` se elimina como en C3‑F. -/
theorem deuda_of_isFC1 (h : DEUDA_evalLiftfc_isFC1) : DEUDA_evalLiftfc := by
  intro v X
  refine prf_ex_elim_imp ?_
  refine PrfH.mp _ _ _ ?_ (prfH_hyp_self _)
  refine prf_to_prfH ?_ _
  refine prf_ex_elim_imp ?_
  refine PrfH.mp _ _ _ ?_ (prfH_hyp_self _)
  simpa only [liftFormula, liftF_targetLiftfc, liftF_isFC1, liftTerm, Nat.reduceAdd,
    Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceGT, reduceIte, if_true]
    using prf_to_prfH (h (.var 1) (.var 0) (liftTerm 0 (liftTerm 0 v))
      (liftTerm 0 (liftTerm 0 X))) _

end ROBINSON_PlusPlus.Meta.EvalLiftfcPrf

/-! ## `export` — por PROPÓSITO DECLARADO

El consumidor previsto es el caso `lift` de `PrfH_tc_objAt` (`Meta/SubstTreeReflect.lean`), que
cerraría los cuatro tags que faltan. Nada lo consume todavía, y se dice en vez de fingir una
medición de consumo. -/
export ROBINSON_PlusPlus.Meta.EvalLiftfcPrf (
  liftfcT liftfcT_termCode evalLiftfcCode targetLiftfc
  liftTerm_evalLiftfcCode substTerm_evalLiftfcCode
  liftF_targetLiftfc substF_targetLiftfc
  DEUDA_evalLiftfc DEUDA_evalLiftfc_isFC1 deuda_of_isFC1
)

/-! ## FOOTPRINT -/

#print axioms ROBINSON_PlusPlus.Meta.EvalLiftfcPrf.liftfcT_termCode
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftfcPrf.deuda_of_isFC1

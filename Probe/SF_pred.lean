/- # SF_pred — la EVALUACION DOTADA de `pred` (sub-obligacion #2 de `pcc_eval_substtc`).

   Objetivo:  `pcc_eval_pred (n) : Prf (provFromCode (eqc (predcT (tcFn n)) (tcFn (pred n))))`
   para `n` **ABSTRACTO**.

   Molde: `Meta/EvalArithPrf.lean` (`pcc_eval_add`) — base + paso + `prf_nat_induction` + `prf_spec`.
   Resulta MAS BARATO que `add`: el paso inductivo **no usa la hipotesis de induccion**
   (`ax26_pred_succ` da el valor directamente), asi que el «paso» es un teorema incondicional.

   ⚠️ CERO axiomas de Lean, cero `sorry`. `predcT` es una DEFINICION y nada mas: no se postula
   ninguna ecuacion de recursion suya (eso seria la familia `ax_tc_*`, INCONSISTENTE). -/
import ROBINSON_PlusPlus.Meta

open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.TcArithPrf ROBINSON_PlusPlus.Meta.CheckArith
open ROBINSON_PlusPlus.Meta.Sigma1Prf ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
open ROBINSON_PlusPlus.Meta.MpCodePrf ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf
open ROBINSON_PlusPlus.Meta.NumCodeClosedPrf ROBINSON_PlusPlus.Meta.EvalArithPrf
open ROBINSON_PlusPlus.Meta.EvalListPrf ROBINSON_PlusPlus.Meta.EvalLtPrf
open ROBINSON_PlusPlus.Meta.EvalNthcPrf ROBINSON_PlusPlus.Meta.NatArithPrf
open ROBINSON_PlusPlus.Meta.DotConsPrf ROBINSON_PlusPlus.Meta.DerivCondPrf
open ROBINSON_PlusPlus.Meta.CodeCtorKit ROBINSON_PlusPlus.Meta.BdAllIntroPrf
open ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.BoundedInPrf

set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

namespace SFPred

/-! ## §1 · El constructor de codigo de `pred` — DEFINICION y nada mas -/

/-- Codigo object del termino `pred x` desde el codigo `x` de su argumento: `⟨1, ⌜τ⌝, [x]⟩`.
    Espeja `termCode` sobre `.func pred_sym [_]`. **Es una definicion**: no se postula ninguna
    ecuacion de recursion para ella. -/
def predcT (x : Term) : Term := funcc (strCode pred_sym) (cons x nil)

/-- **Puente definicional** con `termCode`, por `rfl` (como `addcT_termCode`/`succcT`). -/
theorem predcT_termCode (a : Term) : predcT (termCode a) = termCode (pred a) := rfl

/-- Congruencia META de `predcT`. -/
theorem prf_congr_predcT {x y : Term} (h : Prf (x =eq y)) : Prf (predcT x =eq predcT y) :=
  prf_congr_funcc2 (prf_congr_cons_head h)

/-- `substtc` atraviesa `predcT`. -/
theorem prf_substtc_predcT (v W x : Term) :
    Prf (substtc v W (predcT x) =eq predcT (substtc v W x)) :=
  prf_substtc_funcc1 v W (strCode pred_sym) x

/-- `liftc` atraviesa `predcT`. -/
theorem prf_liftc_predcT (c x : Term) :
    Prf (liftc c (predcT x) =eq predcT (liftc c x)) :=
  prf_eq_trans (prf_liftc_func c (strCode pred_sym) (cons x nil))
    (prf_congr_funcc2
      (prf_eq_trans (prf_liftsc_cons c x nil) (prf_congr_cons_tail (prf_liftsc_nil c))))

/-- `predcT X` es `substtc`-invariante si `X` lo es (descarga las hipotesis del KIT). -/
theorem substtc_inv_predcT {X : Term} (hX : ∀ W, Prf (substtc zero W X =eq X)) :
    ∀ W, Prf (substtc zero W (predcT X) =eq predcT X) :=
  fun W => prf_eq_trans (prf_substtc_predcT zero W X) (prf_congr_predcT (hX W))

/-- Codigo de la formula `τ(ṅ) = (pred n)˙`: *el termino simbolico «predecesor del numeral de `n`»
    es igual al numeral del valor `pred n`*. Es lo que hay que demostrar **dentro** de `Prov`. -/
def evalPredCode (a : Term) : Term := eqCodeFn (predcT (tcFn a)) (tcFn (pred a))

/-! ## §2 · BASE: `n = 0` — sale de `ax25_pred_zero`, que es un axioma CERRADO -/

/-- La instancia codificada de `ax25_pred_zero`, ya computada: `Prov(⌜τ⌜0⌝ = ⌜0⌝⌝)`.
    Al ser el axioma CERRADO no hace falta `substfc` ninguno: `repr_pos'_prf` lo da directo,
    y `formCode (pred 0 = 0) = eqCodeFn (predcT ⌜0⌝) ⌜0⌝` **por `rfl`**. -/
theorem pcc_ax25_computed :
    Prf (provFromCode (eqCodeFn (predcT (termCode zero)) (termCode zero))) :=
  repr_pos'_prf (prf_ax (show ax25_pred_zero ∈ axioms by simp [axioms]))

/-- **BASE de la evaluacion provable de `pred`**: `⊢ Prov(⌜τ(0̇) = (pred 0)˙⌝)`.
    Transporte Leibniz de codigos: `⌜0⌝ =eq tcFn 0` (`prf_tc_zero`) en el argumento, y
    `⌜0⌝ =eq tcFn 0 =eq tcFn (pred 0)` (`prf_congr_tcFn` sobre `ax25`) en el resultado. -/
theorem pcc_eval_pred_zero : Prf (provFromCode (evalPredCode zero)) := by
  have hz : Prf (termCode zero =eq tcFn zero) := prf_eq_symm prf_tc_zero
  have h0 : Prf (pred zero =eq zero) := prf_ax (show ax25_pred_zero ∈ axioms by simp [axioms])
  have hr : Prf (termCode zero =eq tcFn (pred zero)) :=
    prf_eq_trans hz (prf_congr_tcFn (prf_eq_symm h0))
  exact prf_mp (prf_provCode_congr (prf_congr_eqCodeFn (prf_congr_predcT hz) hr))
    pcc_ax25_computed

/-! ## §3 · PASO: `n = σx` — sale de `ax26_pred_succ`, y **NO usa la hipotesis de induccion** -/

/-- El cuerpo de `ax26_pred_succ` (`∀n. τ(σn) = n`). -/
def AX26_BODY : Formula := pred (succ (.var 0)) =eq (.var 0)

theorem AX26_BODY_ok : ax26_pred_succ = Formula.forall AX26_BODY := rfl

/-- `substCodeF` computa la instancia por `rfl`: el testigo-codigo `w` cae en las dos posiciones. -/
theorem substCodeF_AX26 (w : Term) :
    substCodeF 0 w AX26_BODY = eqCodeFn (predcT (succcT w)) w := rfl

/-- La instancia codificada de `ax26_pred_succ` con testigo-codigo **arbitrario** `w`,
    ya computada: `Prov(⌜τ(σw) = w⌝)`. -/
theorem pcc_ax26_computed (w : Term) :
    Prf (provFromCode (eqCodeFn (predcT (succcT w)) w)) := by
  have hmem : Formula.forall AX26_BODY ∈ axioms := by
    show ax26_pred_succ ∈ axioms
    simp [axioms]
  exact prf_mp (prf_provCode_congr (prf_substfc_arith_open 0 w AX26_BODY))
    (pcc_axiom_inst AX26_BODY hmem w)

/-- **PASO de la evaluacion provable de `pred`**, en forma INCONDICIONAL:
    `⊢ Prov(⌜τ((σx)˙) = (pred (σx))˙⌝)` — **sin hipotesis de induccion**.

    Transporte de codigos: `succcT ẋ =eq (σx)˙` (`prf_tc_succ'`) a la izquierda y
    `ẋ =eq (τ(σx))˙` (`prf_congr_tcFn` sobre `prf_pred_succ`) a la derecha. -/
theorem pcc_eval_pred_succ (x : Term) : Prf (provFromCode (evalPredCode (succ x))) := by
  have hL : Prf (predcT (succcT (tcFn x)) =eq predcT (tcFn (succ x))) :=
    prf_congr_predcT (prf_eq_symm (prf_tc_succ' x))
  have hR : Prf (tcFn x =eq tcFn (pred (succ x))) :=
    prf_congr_tcFn (prf_eq_symm (prf_pred_succ x))
  exact prf_mp (prf_provCode_congr (prf_congr_eqCodeFn hL hR)) (pcc_ax26_computed (tcFn x))

/-- La forma IMPLICACION que exige `prf_nat_induction` (la HI se descarta). -/
theorem pcc_eval_pred_succ_imp (x : Term) :
    Prf (provFromCode (evalPredCode x) ⇒ provFromCode (evalPredCode (succ x))) :=
  prf_deduction (prf_to_prfH (pcc_eval_pred_succ x) _)

/-! ## §4 · INDUCCION object: la evaluacion provable de `pred`, COMPLETA -/

/-- `substTerm` atraviesa `evalPredCode` (sus constantes de codigo son cerradas). -/
theorem substTerm_evalPredCode (v : Nat) (s X : Term) :
    substTerm v s (evalPredCode X) = evalPredCode (substTerm v s X) := by
  simp only [evalPredCode, eqCodeFn, predcT, funcc, tcFn, pred, cons, nil, zero, succ,
    substTerm, substTerms, substTerm_numeral, substTerm_strCode]

/-- `liftTerm` atraviesa `evalPredCode`. -/
theorem liftTerm_evalPredCode (k : Nat) (X : Term) :
    liftTerm k (evalPredCode X) = evalPredCode (liftTerm k X) := by
  simp only [evalPredCode, eqCodeFn, predcT, funcc, tcFn, pred, cons, nil, zero, succ,
    liftTerm, liftTerms, liftTerm_numeral, liftTerm_strCode]

/-- Predicado inductivo `Ψ(n) = Prov(⌜τ(ṅ) = (pred n)˙⌝)` (`n` = `#0`). A diferencia de `+`,
    **no hay parametro liftado**: el predicado es cerrado salvo `#0`. -/
def evalPredPred : Formula := provFromCode (evalPredCode (.var 0))

theorem substFormula_evalPredPred (b : Term) :
    substFormula 0 b evalPredPred = provFromCode (evalPredCode b) := by
  simp only [evalPredPred, substFormula_provFromCode_open, substTerm_evalPredCode, substTerm,
    if_true]

theorem step_evalPredPred :
    substFormula 0 (succ (.var 0)) (liftFormula 1 (provFromCode (evalPredCode (.var 0))))
      = provFromCode (evalPredCode (succ (.var 0))) := by
  rw [liftFormula_provFromCode_open, liftTerm_evalPredCode, substFormula_provFromCode_open,
    substTerm_evalPredCode]
  simp only [liftTerm, substTerm, Nat.zero_lt_one, reduceIte, Nat.lt_irrefl, if_true]

/-- **EVALUACION PROVABLE DE `pred` (∀ object)**: `⊢ ∀n. Prov(⌜τ(ṅ) = (pred n)˙⌝)`. -/
theorem prf_eval_pred_all : Prf (Formula.forall evalPredPred) := by
  refine prf_nat_induction evalPredPred ?base ?step
  · rw [substFormula_evalPredPred]
    exact pcc_eval_pred_zero
  · refine Prf.gen _ ?_
    show Prf (Formula.impl (provFromCode (evalPredCode (.var 0)))
      (substFormula 0 (succ (.var 0))
        (liftFormula 1 (provFromCode (evalPredCode (.var 0))))))
    rw [step_evalPredPred]
    exact pcc_eval_pred_succ_imp (.var 0)

/-- **EVALUACION PROVABLE DE `pred`**: `⊢ Prov(⌜τ(ṅ) = (pred n)˙⌝)` para `n` **ARBITRARIO**.
    Es la sub-obligacion #2 de `pcc_eval_substtc`, CERRADA. -/
theorem pcc_eval_pred (n : Term) : Prf (provFromCode (evalPredCode n)) := by
  have h := prf_spec prf_eval_pred_all n
  rwa [substFormula_evalPredPred] at h

/-- La misma, escrita con `eqc` (que es `eqCodeFn` por `rfl`) — la forma del encargo. -/
theorem pcc_eval_pred' (n : Term) :
    Prf (provFromCode (eqc (predcT (tcFn n)) (tcFn (pred n)))) := pcc_eval_pred n

/-! ## §5 · CONGRUENCIA INTERNA de `predcT` (dentro de `Prov`) — la pieza que consume el
consumidor aguas abajo, molde `pcc_congr_succ_code` (`Meta/EvalArithPrf.lean:253`). -/

theorem pcc_congr_predcT_code (X Y : Term) (hX : ∀ W, Prf (substtc zero W X =eq X))
    (heq : Prf (provFromCode (eqc X Y))) :
    Prf (provFromCode (eqc (predcT X) (predcT Y))) := by
  let Ac : Term := eqc (predcT X) (predcT (varc (numeral 0)))
  have hcomp : ∀ t : Term, Prf (substfc zero t Ac =eq eqc (predcT X) (predcT t)) := by
    intro t
    refine prf_eq_trans (prf_substfc_eq zero t (predcT X) (predcT (varc (numeral 0)))) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · exact prf_eq_trans (prf_substtc_predcT zero t X) (prf_congr_predcT (hX t))
    · exact prf_eq_trans (prf_substtc_predcT zero t (varc (numeral 0)))
        (prf_congr_predcT (prf_substtc_varc0 t))
  have hAX : Prf (provFromCode (substfc zero X Ac)) :=
    prf_mp (prf_provCode_congr (prf_eq_symm (hcomp X)))
      (prf_provFromCode_eqCodeFn_refl (predcT X))
  have hAY : Prf (provFromCode (substfc zero Y Ac)) := pcc_leibniz_apply Ac X Y heq hAX
  exact prf_mp (prf_provCode_congr (hcomp Y)) hAY

/-! ## §5b · PAYOFF: el LADO DERECHO de `ax_substtc_var_gt` dotado, YA PLEGADO.

Al dotar `ax_substtc_var_gt` con testigos-codigo `v̇ ṡ ṅ`, `substCodeF` computa

```text
  lt v̇ ṅ  ⇒  substtcT v̇ ṡ (unT 0 ṅ)  =  unT 0 (predcT ṅ)
```

(`varc x = ⟨0,x⟩` es EXACTAMENTE `unT 0`, por `rfl` — ver `varc_es_un0`). El unico obstaculo
para plegar `unT 0 (predcT ṅ)` en `(varc (pred n))˙` era `predcT ṅ ↦ (pred n)˙`, o sea
`pcc_eval_pred`. Con el en la mano el plegado sale con SOLO piezas de produccion. -/

/-- `varc` **es** el constructor unario de tag 0: por `rfl`. -/
theorem varc_es_un0 (n : Term) : varc n = cons (numeralM 0) (cons n nil) := rfl

/-- `tcFn (varc n) = unT 0 ṅ`, dentro de `Prov`. Instancia de `pcc_dot_un` — pieza de produccion. -/
theorem pcc_dot_varc (n : Term) :
    Prf (provFromCode (eqCodeFn (unT 0 (tcFn n)) (tcFn (varc n)))) := pcc_dot_un 0 n

/-- **EL LADO DERECHO DE `ax_substtc_var_gt`, DOTADO Y PLEGADO**:
    `⊢ Prov(⌜ ⟨0, τ(ṅ)⟩ = (varc (pred n))˙ ⌝)` para `n` **ABSTRACTO**.

    Es `pcc_eval_pred` bajo `unT 0` (`pcc_congr_unT_code`) encadenado con `pcc_dot_un`
    (`pcc_eq_trans_code`). Confirma que la pieza **hace falta y encaja**: sin ella el `predcT`
    se queda ahi y no hay forma de llegar a `(varc (pred n))˙`. -/
theorem pcc_eval_varc_pred (n : Term) :
    Prf (provFromCode (eqc (unT 0 (predcT (tcFn n))) (tcFn (varc (pred n))))) :=
  pcc_eq_trans_code _ _ _
    (substtc_inv_unT (substtc_inv_predcT (substtc_inv_tcFn n)))
    (prf_mp (pcc_congr_unT_code 0 (predcT (tcFn n)) (tcFn (pred n))
      (substtc_inv_predcT (substtc_inv_tcFn n))) (pcc_eval_pred n))
    (pcc_dot_varc (pred n))

/-! ## §6 · CONTROL NEGATIVO: el enunciado NO es una reflexividad disfrazada.
`predcT (tcFn n)` y `tcFn (pred n)` son codigos DISTINTOS a nivel Lean — igual que en
`evalSubstfcCode`. Lo que se ha probado es una evaluacion de verdad, no un `rfl`. -/

set_option linter.unusedVariables false in
example (n : Term) : True := by
  fail_if_success exact (rfl : predcT (tcFn n) = tcFn (pred n))
  trivial

/-- Y en cambio con `termCode` (codigo META, no el simbolo opaco `tcFn`) SI es `rfl`:
    la diferencia entre los dos es exactamente el contenido del teorema. -/
example (n : Term) : predcT (termCode n) = termCode (pred n) := rfl

/-! ## §7 · ¿HACE FALTA? — la medida del uso en `ax_substtc_var_gt`

`ax_substtc_var_gt : ∀v∀s∀n. v < n ⇒ substtc v s (varc n) = varc (pred n)`.

Al dotarla con testigos-codigo `v̇ ṡ ṅ` el lado derecho sale como `varcT (predcT ṅ)` — un
**`predcT` sobre codigo abstracto**, que hay que convertir en `(pred n)˙` para poder plegar
`varcT (…) ↦ (varc (pred n))˙` con el KIT. Eso es EXACTAMENTE `pcc_eval_pred`.

La alternativa («que `n` venga como `σm` en el punto de uso») se mide aqui abajo: el caso `σ`
**se cierra sin induccion y sin `pcc_eval_pred`**, pero el caso `0` tambien hace falta porque el
recorrido de `pcc_eval_substtc` recibe el codigo `varc n` con `n` **abstracto** (no hay forma
meta de partirlo). La guarda `v < n` no da un `m` a nivel Lean: solo da un ∃ OBJETO. -/

/-- (i) Si el `n` del punto de uso ya viniera como `σm`, esto basta — **sin induccion**. -/
theorem pcc_eval_pred_of_succ (m : Term) :
    Prf (provFromCode (evalPredCode (succ m))) := pcc_eval_pred_succ m

/-- (ii) Pero con `n` abstracto la unica salida a nivel LEAN seria una disyuncion meta, que no
    existe: lo que la teoria da es `prf_zero_or_eq_succ_pred`, una disyuncion **OBJETO**
    (`n = 0 ∨ n = σ(τ n)`), inutilizable para partir un `Term` de Lean. Por eso la induccion
    object de §4 es la ruta correcta, y por eso la pieza SI hace falta. -/
example (m : Term) : Prf (lor (Formula.eq m zero) (Formula.eq m (succ (pred m)))) :=
  prf_zero_or_eq_succ_pred m

end SFPred

#print axioms SFPred.pcc_eval_pred
#print axioms SFPred.pcc_eval_pred'
#print axioms SFPred.pcc_eval_pred_zero
#print axioms SFPred.pcc_eval_pred_succ
#print axioms SFPred.prf_eval_pred_all
#print axioms SFPred.pcc_congr_predcT_code
#print axioms SFPred.predcT_termCode
#print axioms SFPred.substCodeF_AX26
#print axioms SFPred.varc_es_un0
#print axioms SFPred.pcc_dot_varc
#print axioms SFPred.pcc_eval_varc_pred

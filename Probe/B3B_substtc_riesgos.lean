/-
# `Probe/B3B_substtc_riesgos.lean` — COLISIONES y DEDUPLICACION de `sondeos/EvalSubsttc.lean`

Angulo: **el riesgo de nombre**. No promueve nada; deja COMPILADO cada veredicto.

Fichero auditado: `sondeos/EvalSubsttc.lean`, md5 `7cfc61a8f12477b3dae118a136d5b904`,
**1905 lineas, 156 declaraciones** (medido hoy 2026-09-04; el fichero no se ha tocado desde
el 09-01 13:14).

## Metodo

No copio el sondeo. Copio **solo los TIPOS** que hacen falta (`SF`, §1) — que son `def`s
baratos — y comparo cada tipo del sondeo contra el tipo de la constante de produccion:

* `abbrev S_x : Prop` = el enunciado del SONDEO, transcrito;
* `abbrev P_x : Prop` = el enunciado de PRODUCCION, transcrito, y **certificado** acto seguido
  con `example : P_x := <constante de produccion>`: si me hubiera equivocado al transcribirlo,
  ese `example` no elabora;
* el veredicto: `fail_if_success (have : S_x = P_x := rfl)`. `S_x` y `P_x` son dos habitantes
  de `Prop`, asi que `rfl` entre ellos NO se cierra por irrelevancia de pruebas: exige que los
  dos ENUNCIADOS sean defeq. Que falle **es** la divergencia.

⚠️ El arnes se controla en §0: el mismo `fail_if_success` sobre un `rfl` que SI vale tiene que
fallar-al-fallar, y §3 exhibe los homonimos que **no** divergen (donde el `rfl` cierra).

    lake env lean Probe/B3B_substtc_riesgos.lean
-/
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
open ROBINSON_PlusPlus.Meta.HilbertDeduction ROBINSON_PlusPlus.Meta.BoundedInPrf
open ROBINSON_PlusPlus.Meta.ChainPrf ROBINSON_PlusPlus.Meta.StrongInductionPrf
open ROBINSON_PlusPlus.Meta.EvalPredPrf

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

namespace B3B

/-! ############################################################################
    ## §0 · EL ARNES — control POSITIVO y NEGATIVO
    ############################################################################ -/

abbrev CTL_A : Prop := ∀ n : Term, Prf (n =eq n)
abbrev CTL_B : Prop := ∀ m : Term, Prf (m =eq m)
abbrev CTL_C : Prop := ∀ n : Term, Prf (succ n =eq n)

/-- POSITIVO: dos transcripciones del MISMO enunciado si cierran por `rfl`. -/
theorem ctl_pos : CTL_A = CTL_B := rfl

/-- NEGATIVO: dos enunciados distintos NO cierran — y el `fail_if_success` lo detecta. -/
example : True := by
  fail_if_success (have : CTL_A = CTL_C := rfl)
  trivial

/-- CONTROL DEL CONTROL: si el `fail_if_success` fuera vacuo, este `example` no compilaria,
    porque aqui el `have` SI tiene exito. -/
example : True := by
  fail_if_success (fail_if_success (have : CTL_A = CTL_B := rfl))
  trivial

/-! ############################################################################
    ## §1 · `SF` — los TIPOS del sondeo (solo `def`s; ninguna prueba se recopila)
    ############################################################################ -/

namespace SF

/-- `sondeos/EvalSubsttc.lean` §1 (`substtcT`). -/
def substtcT (v s t : Term) : Term :=
  funcc (strCode "substtc") (cons v (cons s (cons t nil)))
/-- `sondeos/EvalSubsttc.lean` §1 (`substtscT`). -/
def substtscT (v s ts : Term) : Term :=
  funcc (strCode "substtsc") (cons v (cons s (cons ts nil)))

/-- `sondeos/EvalSubsttc.lean` §5 (`targetSubsttc`). -/
def targetSubsttc (v s X : Term) : Formula :=
  provFromCode (eqc (substtcT (tcFn v) (tcFn s) (tcFn X)) (tcFn (substtc v s X)))
/-- `sondeos/EvalSubsttc.lean` §5 (`targetSubsttsc`). -/
def targetSubsttsc (v s X : Term) : Formula :=
  provFromCode (eqc (substtscT (tcFn v) (tcFn s) (tcFn X)) (tcFn (substtsc v s X)))

/-- `sondeos/EvalSubsttc.lean` §10 (`PredHyp`). -/
def PredHyp : Prop := ∀ v n : Term,
  Prf (Formula.impl (lt v n) (provFromCode (eqc (predcT (tcFn n)) (tcFn (pred n)))))

/-- `sondeos/EvalSubsttc.lean` §11 (`CONJ`). `isTC1`/`wfAll1`/`argsIn` son los de PRODUCCION:
    el sondeo los copia LETRA POR LETRA (se certifica en §4). -/
def CONJ (w v s X : Term) : Formula :=
  land (Formula.impl (isTC1 w X) (targetSubsttc v s X))
       (Formula.impl (land (wfAll1 w) (argsIn w X)) (targetSubsttsc v s X))

/-- `sondeos/EvalSubsttc.lean` §11 (`PHIbody`). -/
def PHIbody : Formula := CONJ (.var 2) (.var 1) (.var 0) (.var 3)
/-- `sondeos/EvalSubsttc.lean` §11 (`PHI`) — **TRES** cuantificadores. -/
def PHI : Formula := Formula.forall (Formula.forall (Formula.forall PHIbody))

/-- `sondeos/EvalSubsttc.lean` §11 (`PSI3`). -/
def PSI3 : Formula := liftFormula 0 (liftFormula 0 (liftFormula 0 (PSI PHI)))

end SF

/-! CONTROL: `targetSubsttc` NO es una reflexividad disfrazada (mismo control negativo que
    trae el sondeo). -/
example (v s X : Term) : True := by
  fail_if_success
    exact (rfl : SF.substtcT (tcFn v) (tcFn s) (tcFn X) = tcFn (substtc v s X))
  trivial

/-! ############################################################################
    ## §2 · LAS 17 COLISIONES — el homonimo de produccion habla de `liftc`, no de `substtc`
    ############################################################################ -/

/-! ### 2.1 · `refl_caso_funcc` — `Meta/LiftcCodePrf.lean` (`refl_caso_funcc`) -/

abbrev S01 : Prop := ∀ (v s X p b : Term), Prf (X =eq funcc p b) →
  Prf (SF.targetSubsttsc v s b) → Prf (SF.targetSubsttc v s X)
abbrev P01 : Prop := ∀ (s p b : Term), Prf (s =eq funcc p b) →
  Prf (ROBINSON_PlusPlus.Meta.LiftcCodePrf.targetLiftsc b) →
  Prf (ROBINSON_PlusPlus.Meta.LiftcCodePrf.targetLift s)
example : P01 := ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_caso_funcc
example : True := by
  fail_if_success (have : S01 = P01 := rfl)
  trivial

/-! ### 2.2 · `refl_lista_nil` -/

abbrev S02 : Prop := ∀ (v s : Term), Prf (SF.targetSubsttsc v s nil)
abbrev P02 : Prop := Prf (ROBINSON_PlusPlus.Meta.LiftcCodePrf.targetLiftsc nil)
example : P02 := ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_lista_nil
example : True := by
  fail_if_success (have : S02 = P02 := rfl)
  trivial

/-! ### 2.3 · `refl_lista_cons` -/

abbrev S03 : Prop := ∀ (v s h t : Term), Prf (SF.targetSubsttc v s h) →
  Prf (SF.targetSubsttsc v s t) → Prf (SF.targetSubsttsc v s (cons h t))
abbrev P03 : Prop := ∀ (h t : Term),
  Prf (ROBINSON_PlusPlus.Meta.LiftcCodePrf.targetLift h) →
  Prf (ROBINSON_PlusPlus.Meta.LiftcCodePrf.targetLiftsc t) →
  Prf (ROBINSON_PlusPlus.Meta.LiftcCodePrf.targetLiftsc (cons h t))
example : P03 := ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_lista_cons
example : True := by
  fail_if_success (have : S03 = P03 := rfl)
  trivial

/-! ### 2.4 · `refl_caso_varc` -/

abbrev S04 : Prop := ∀ (v s X n : Term), Prf (X =eq varc n) →
  Prf (Formula.impl (lt v n) (provFromCode (eqc (predcT (tcFn n)) (tcFn (pred n))))) →
  Prf (SF.targetSubsttc v s X)
abbrev P04 : Prop := ∀ (s a : Term), Prf (s =eq varc a) →
  Prf (ROBINSON_PlusPlus.Meta.LiftcCodePrf.targetLift s)
example : P04 := ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_caso_varc
example : True := by
  fail_if_success (have : S04 = P04 := rfl)
  trivial

/-! ### 2.5 · `refl_shapeUn_imp` -/

abbrev S05 : Prop := ∀ (_ : SF.PredHyp) (v s X : Term),
  Prf (Formula.impl (shapeUn X 0) (SF.targetSubsttc v s X))
abbrev P05 : Prop := ∀ (X : Term),
  Prf (Formula.impl (shapeUn X 0) (ROBINSON_PlusPlus.Meta.LiftcCodePrf.targetLift X))
example : P05 := ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_shapeUn_imp
example : True := by
  fail_if_success (have : S05 = P05 := rfl)
  trivial

/-! ### 2.6 · `refl_caso_funcc_imp` -/

abbrev S06 : Prop := ∀ (v s p b : Term),
  Prf (Formula.impl (SF.targetSubsttsc v s b) (SF.targetSubsttc v s (funcc p b)))
abbrev P06 : Prop := ∀ (p b : Term),
  Prf (Formula.impl (ROBINSON_PlusPlus.Meta.LiftcCodePrf.targetLiftsc b)
    (ROBINSON_PlusPlus.Meta.LiftcCodePrf.targetLift (funcc p b)))
example : P06 := ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_caso_funcc_imp
example : True := by
  fail_if_success (have : S06 = P06 := rfl)
  trivial

/-! ### 2.7 · `refl_shapeBin_imp` -/

abbrev S07 : Prop := ∀ (v s X : Term),
  Prf (Formula.impl (land (shapeBin X 1) (SF.targetSubsttsc v s (nthc X (numeralM 2))))
    (SF.targetSubsttc v s X))
abbrev P07 : Prop := ∀ (X : Term),
  Prf (Formula.impl (land (shapeBin X 1)
      (ROBINSON_PlusPlus.Meta.LiftcCodePrf.targetLiftsc (nthc X (numeralM 2))))
    (ROBINSON_PlusPlus.Meta.LiftcCodePrf.targetLift X))
example : P07 := ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_shapeBin_imp
example : True := by
  fail_if_success (have : S07 = P07 := rfl)
  trivial

/-! ### 2.8 · `refl_lista_cons_imp` -/

abbrev S08 : Prop := ∀ (v s h t : Term),
  Prf (Formula.impl (land (SF.targetSubsttc v s h) (SF.targetSubsttsc v s t))
    (SF.targetSubsttsc v s (cons h t)))
abbrev P08 : Prop := ∀ (h t : Term),
  Prf (Formula.impl (land (ROBINSON_PlusPlus.Meta.LiftcCodePrf.targetLift h)
      (ROBINSON_PlusPlus.Meta.LiftcCodePrf.targetLiftsc t))
    (ROBINSON_PlusPlus.Meta.LiftcCodePrf.targetLiftsc (cons h t)))
example : P08 := ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_lista_cons_imp
example : True := by
  fail_if_success (have : S08 = P08 := rfl)
  trivial

/-! ### 2.9 · `PHIbody` — colision de **VALOR**: los dos son `Formula`, el TIPO no distingue.
    ⚠️ Esta y la 2.10 son las dos peores: un `open` mal puesto resuelve al `PHI` equivocado y
    **el fichero sigue tipando** (§6). -/

example : True := by
  fail_if_success (have : SF.PHIbody = ROBINSON_PlusPlus.Meta.EvalLiftcPrf.PHIbody := rfl)
  trivial

/-! ### 2.10 · `PHI` — colision de VALOR. -/

example : True := by
  fail_if_success (have : SF.PHI = ROBINSON_PlusPlus.Meta.EvalLiftcPrf.PHI := rfl)
  trivial

/-! ### 2.11 · `PHI_at` -/

abbrev S11 : Prop := ∀ (t : Term), substFormula 0 t SF.PHI
  = Formula.forall (Formula.forall (Formula.forall
      (SF.CONJ (.var 2) (.var 1) (.var 0) (liftTerm 0 (liftTerm 0 (liftTerm 0 t))))))
abbrev P11 : Prop := ∀ (t : Term),
  substFormula 0 t ROBINSON_PlusPlus.Meta.EvalLiftcPrf.PHI
    = Formula.forall (
        land (Formula.impl (isTC1 (.var 0) (liftTerm 0 t))
               (ROBINSON_PlusPlus.Meta.LiftcCodePrf.targetLift (liftTerm 0 t)))
             (Formula.impl (land (wfAll1 (.var 0)) (argsIn (.var 0) (liftTerm 0 t)))
               (ROBINSON_PlusPlus.Meta.LiftcCodePrf.targetLiftsc (liftTerm 0 t))))
example : P11 := ROBINSON_PlusPlus.Meta.EvalLiftcPrf.PHI_at
example : True := by
  fail_if_success (have : S11 = P11 := rfl)
  trivial

/-! ### 2.12 · `PHI_use` -/

abbrev S12 : Prop := ∀ (Γ : List Formula) (t w v s : Term),
  PrfH Γ (substFormula 0 t SF.PHI) → PrfH Γ (SF.CONJ w v s t)
abbrev P12 : Prop := ∀ (Γ : List Formula) (t w : Term),
  PrfH Γ (substFormula 0 t ROBINSON_PlusPlus.Meta.EvalLiftcPrf.PHI) →
  PrfH Γ (land (Formula.impl (isTC1 w t)
                 (ROBINSON_PlusPlus.Meta.LiftcCodePrf.targetLift t))
               (Formula.impl (land (wfAll1 w) (argsIn w t))
                 (ROBINSON_PlusPlus.Meta.LiftcCodePrf.targetLiftsc t)))
example : P12 := fun Γ t w h => @ROBINSON_PlusPlus.Meta.EvalLiftcPrf.PHI_use Γ t w h
example : True := by
  fail_if_success (have : S12 = P12 := rfl)
  trivial

/-! ### 2.13 · `PSI_inst` — el homonimo de produccion es `Meta/StrongInductionPrf.lean`,
    GENERICO en `Φ` y a UN nivel de `liftFormula`; el del sondeo esta instanciado a `PHI` y a
    TRES niveles. -/

abbrev S13 : Prop := ∀ (Γ : List Formula), PrfH Γ SF.PSI3 → ∀ (z : Term),
  PrfH Γ (Formula.impl (lt z (.var 3)) (substFormula 0 z SF.PHI))
abbrev P13 : Prop := ∀ (Φ : Formula), liftFormula 1 Φ = Φ → ∀ (Γ : List Formula),
  PrfH Γ (liftFormula 0 (PSI Φ)) → ∀ (z : Term),
  PrfH Γ (Formula.impl (lt z (.var 1)) (substFormula 0 z Φ))
example : P13 := fun Φ hΦ Γ h z =>
  @ROBINSON_PlusPlus.Meta.StrongInductionPrf.PSI_inst Φ hΦ Γ h z
example : True := by
  fail_if_success (have : S13 = P13 := rfl)
  trivial

/-! ### 2.14 · `PHI_step` -/

abbrev S14 : Prop := ∀ (_ : SF.PredHyp),
  Prf (Formula.forall (Formula.impl (PSI SF.PHI) SF.PHI))
abbrev P14 : Prop := Prf (Formula.forall (Formula.impl
  (PSI ROBINSON_PlusPlus.Meta.EvalLiftcPrf.PHI) ROBINSON_PlusPlus.Meta.EvalLiftcPrf.PHI))
example : P14 := ROBINSON_PlusPlus.Meta.EvalLiftcPrf.PHI_step
example : True := by
  fail_if_success (have : S14 = P14 := rfl)
  trivial

/-! ### 2.15 · `PHI_all` -/

abbrev S15 : Prop := ∀ (_ : SF.PredHyp) (t : Term), Prf (substFormula 0 t SF.PHI)
abbrev P15 : Prop := ∀ (t : Term),
  Prf (substFormula 0 t ROBINSON_PlusPlus.Meta.EvalLiftcPrf.PHI)
example : P15 := ROBINSON_PlusPlus.Meta.EvalLiftcPrf.PHI_all
example : True := by
  fail_if_success (have : S15 = P15 := rfl)
  trivial

/-! ### 2.16 · `DESCENSO_imp` -/

abbrev S16 : Prop := ∀ (_ : SF.PredHyp) (w v s t : Term),
  Prf (Formula.impl (isTC1 w t) (SF.targetSubsttc v s t))
abbrev P16 : Prop := ∀ (w s : Term),
  Prf (Formula.impl (isTC1 w s) (ROBINSON_PlusPlus.Meta.LiftcCodePrf.targetLift s))
example : P16 := ROBINSON_PlusPlus.Meta.EvalLiftcPrf.DESCENSO_imp
example : True := by
  fail_if_success (have : S16 = P16 := rfl)
  trivial

/-! ### 2.17 · `DESCENSO_lista_imp` -/

abbrev S17 : Prop := ∀ (_ : SF.PredHyp) (w v s t : Term),
  Prf (Formula.impl (land (wfAll1 w) (argsIn w t)) (SF.targetSubsttsc v s t))
abbrev P17 : Prop := ∀ (w s : Term),
  Prf (Formula.impl (land (wfAll1 w) (argsIn w s))
    (ROBINSON_PlusPlus.Meta.LiftcCodePrf.targetLiftsc s))
example : P17 := ROBINSON_PlusPlus.Meta.EvalLiftcPrf.DESCENSO_lista_imp
example : True := by
  fail_if_success (have : S17 = P17 := rfl)
  trivial


/-! ############################################################################
    ## §3 · LOS HOMONIMOS QUE **NO** DIVERGEN — el `rfl` cierra (control del §2)
    ############################################################################

    De los **85** nombres del sondeo que ya existen en produccion, **68 son el MISMO
    enunciado** y solo 17 divergen (§2). Aqui se cierra la clasificacion por los dos lados:
    los tres casos donde el texto difiere pero el TIPO no, y una muestra de los identicos. -/

/-! ### 3.1 · `predcT_termCode` — el texto difiere SOLO en el nombre del ligado (`x` vs `a`). -/

abbrev S_predcT_termCode : Prop := ∀ (x : Term), predcT (termCode x) = termCode (pred x)
abbrev P_predcT_termCode : Prop := ∀ (a : Term), predcT (termCode a) = termCode (pred a)
example : P_predcT_termCode := ROBINSON_PlusPlus.Meta.EvalPredPrf.predcT_termCode
theorem no_colisiona_predcT_termCode : S_predcT_termCode = P_predcT_termCode := rfl

/-! ### 3.2 · `pcc_thm_inst4` / `pcc_axiom_inst4` — el sondeo escribe `succ zero`,
    produccion `numeral 1`. **NO es una colision**: `numeral (n+1) = succ (numeral n)` por
    definicion, luego los dos enunciados son defeq y el `rfl` cierra. -/

abbrev S_pcc_thm_inst4 : Prop := ∀ (φ : Formula), Prf (forall_4 φ) → ∀ (w₁ w₂ w₃ w₄ : Term),
  Prf (provFromCode (substfc zero w₄ (substfc (succ zero) (liftc zero w₃)
    (substfc (succ (succ zero)) (liftc zero (liftc zero w₂))
      (substfc (succ (succ (succ zero))) (liftc zero (liftc zero (liftc zero w₁)))
        (formCode φ))))))
abbrev P_pcc_thm_inst4 : Prop := ∀ (φ : Formula), Prf (forall_4 φ) → ∀ (w₁ w₂ w₃ w₄ : Term),
  Prf (provFromCode (substfc zero w₄ (substfc (numeral 1) (liftc zero w₃)
    (substfc (numeral 2) (liftc zero (liftc zero w₂))
      (substfc (numeral 3) (liftc zero (liftc zero (liftc zero w₁))) (formCode φ))))))
example : P_pcc_thm_inst4 := ROBINSON_PlusPlus.Meta.MpCodePrf.pcc_thm_inst4
theorem no_colisiona_pcc_thm_inst4 : S_pcc_thm_inst4 = P_pcc_thm_inst4 := rfl

abbrev S_pcc_axiom_inst4 : Prop := ∀ (φ : Formula), List.Mem (forall_4 φ) axioms →
  ∀ (w₁ w₂ w₃ w₄ : Term),
  Prf (provFromCode (substfc zero w₄ (substfc (succ zero) (liftc zero w₃)
    (substfc (succ (succ zero)) (liftc zero (liftc zero w₂))
      (substfc (succ (succ (succ zero))) (liftc zero (liftc zero (liftc zero w₁)))
        (formCode φ))))))
abbrev P_pcc_axiom_inst4 : Prop := ∀ (φ : Formula), List.Mem (forall_4 φ) axioms →
  ∀ (w₁ w₂ w₃ w₄ : Term),
  Prf (provFromCode (substfc zero w₄ (substfc (numeral 1) (liftc zero w₃)
    (substfc (numeral 2) (liftc zero (liftc zero w₂))
      (substfc (numeral 3) (liftc zero (liftc zero (liftc zero w₁))) (formCode φ))))))
example : P_pcc_axiom_inst4 := ROBINSON_PlusPlus.Meta.MpCodePrf.pcc_axiom_inst4
theorem no_colisiona_pcc_axiom_inst4 : S_pcc_axiom_inst4 = P_pcc_axiom_inst4 := rfl

/-! ### 3.3 · Las DEFINICIONES copiadas: el cuerpo del sondeo es el de produccion, por `rfl`.
    (Comparar TIPOS de `def`s no dice nada — todas son `Term → … → Formula`.) -/

theorem body_shapeUn (X : Term) (k : Nat) :
    shapeUn X k = Formula.eq X (cons (numeralM k) (cons (nthc X (numeralM 1)) nil)) := rfl
theorem body_shapeBin (X : Term) (k : Nat) :
    shapeBin X k = Formula.eq X (cons (numeralM k)
      (cons (nthc X (numeralM 1)) (cons (nthc X (numeralM 2)) nil))) := rfl
theorem body_argsInBody (wT Y : Term) :
    argsInBody wT Y = Formula.impl (lt (.var 0) (liftTerm 0 (lenc Y)))
      (In (nthc (liftTerm 0 Y) (.var 0)) (liftTerm 0 wT)) := rfl
theorem body_argsIn (wT Y : Term) : argsIn wT Y = Formula.forall (argsInBody wT Y) := rfl
theorem body_isTermCodeE1 (wT X : Term) :
    isTermCodeE1 wT X
      = lor (shapeUn X 0) (land (shapeBin X 1) (argsIn wT (nthc X (numeralM 2)))) := rfl
theorem body_consOk (X : Term) : consOk X = Formula.eq X (cons (carc X) (cdrc X)) := rfl
theorem body_wfAll1Body (w : Term) :
    ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.wfAll1Body w = Formula.impl (lt (.var 0) (liftTerm 0 (lenc w)))
      (isTermCodeE1 (liftTerm 0 w) (nthc (liftTerm 0 w) (.var 0))) := rfl
theorem body_wfAll1 (w : Term) :
    wfAll1 w = Formula.forall (ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.wfAll1Body w) := rfl
theorem body_isTC1 (w c : Term) : isTC1 w c = land (wfAll1 w) (In c w) := rfl
theorem body_hasWit (c : Term) : hasWit c = Formula.ex (isTC1 (.var 0) (liftTerm 0 c)) := rfl
theorem body_nilOrCons :
    ROBINSON_PlusPlus.Meta.EvalLiftcPrf.nilOrCons
      = lor (Formula.eq (.var 0) nil) (consOk (.var 0)) := rfl
theorem body_varcT (X : Term) :
    ROBINSON_PlusPlus.Meta.LiftcCodePrf.varcT X = unT 0 X := rfl
theorem body_funccT (X Y : Term) :
    ROBINSON_PlusPlus.Meta.LiftcCodePrf.funccT X Y = binT 1 X Y := rfl
theorem body_predcT (x : Term) : predcT x = funcc (strCode pred_sym) (cons x nil) := rfl
theorem body_AX26_BODY :
    ROBINSON_PlusPlus.Meta.EvalPredPrf.AX26_BODY = (pred (succ (.var 0)) =eq (.var 0)) := rfl

/-! ### 3.4 · Muestra de TEOREMAS identicos, uno por modulo de destino: el enunciado del
    sondeo, habitado por la constante de PRODUCCION. -/

-- `Meta/CodeCtorKit.lean` (⚠️ NO `LiftcCodePrf`: subieron hoy, en esta misma rama B3)
example (v : Nat) (W t : Term) (ht : ∀ c : Nat, liftTerm c t = t) :
    Prf (substtc (numeral v) W (termCode t) =eq termCode t) :=
  ROBINSON_PlusPlus.Meta.CodeCtorKit.prf_substtc_termCode_closed v W t ht
-- `Meta/EvalArithPrf.lean` (KIT TERNARIO, entrado hoy)
example (v W sc x y z : Term) :
    Prf (substtc v W (funcc sc (cons x (cons y (cons z nil))))
      =eq funcc sc (cons (substtc v W x) (cons (substtc v W y) (cons (substtc v W z) nil)))) :=
  ROBINSON_PlusPlus.Meta.EvalArithPrf.prf_substtc_funcc3 v W sc x y z
-- `Meta/LiftcCodePrf.lean`
example (v : Nat) (W a : Term) :
    Prf (substtc (numeral v) W (ROBINSON_PlusPlus.Meta.LiftcCodePrf.varcT a)
      =eq ROBINSON_PlusPlus.Meta.LiftcCodePrf.varcT (substtc (numeral v) W a)) :=
  ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_substtc_varcT_at v W a
-- `Meta/EvalPredPrf.lean`
example (v W x : Term) : Prf (substtc v W (predcT x) =eq predcT (substtc v W x)) :=
  ROBINSON_PlusPlus.Meta.EvalPredPrf.prf_substtc_predcT v W x
-- `Meta/CodeWitnessPrf.lean` (`SinWTs`)
example (w hd tl : Term) :
    Prf (Formula.impl (argsIn w (cons hd tl)) (argsIn w tl)) :=
  ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.prf_argsIn_tail w hd tl
-- `Meta/CodeWitnessPrf.lean` (`ENS`)
example (v : Nat) (s w c : Term) :
    substFormula v s (isTC1 w c) = isTC1 (substTerm v s w) (substTerm v s c) :=
  ROBINSON_PlusPlus.Meta.CodeWitnessPrf.ENS.substF_isTC1 v s w c
-- `Meta/EvalLiftcPrf.lean`
example (Y : Term) : Prf (lor (Formula.eq Y nil) (consOk Y)) :=
  ROBINSON_PlusPlus.Meta.EvalLiftcPrf.prf_nil_or_cons Y

/-! ############################################################################
    ## §4 · DUPLICADOS DE VERDAD: el sondeo NO los tiene por nombre, pero ya estan
    ############################################################################ -/

/-! ### 4.1 · `eqc_eq_eqCodeFn` (sondeo :64) — es `Sigma1AtomPrf.eqCodeFn_eq_eqc` con la
    ORIENTACION INVERTIDA, y produccion ya lo tiene registrado con nombre propio. -/

theorem dup_eqc_por_symm (a b : Term) : eqc a b = eqCodeFn a b :=
  (ROBINSON_PlusPlus.Meta.Sigma1AtomPrf.eqCodeFn_eq_eqc a b).symm
theorem dup_eqc_ya_esta : ∀ (a b : Term), eqc a b = eqCodeFn a b :=
  ROBINSON_PlusPlus.Meta.EvalLiftcPrf.eqc_eq_eqCodeFn_es_symm

/-! ### 4.2 · `PrfH_congr_pred` (sondeo :1796) — es `BoundedInPrf.PrfH_eq_congr_pred`. -/

theorem dup_PrfH_congr_pred {Γ : List Formula} {a b : Term} (h : PrfH Γ (a =eq b)) :
    PrfH Γ (pred a =eq pred b) :=
  ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_eq_congr_pred h

/-! ### 4.3 · `liftT_predcode` (sondeo :1823) — es `EvalPredPrf.liftTerm_evalPredCode`
    con `evalPredCode` desplegado (`rfl`). -/

theorem dup_liftT_predcode (k : Nat) (n : Term) :
    liftTerm k (eqc (predcT (tcFn n)) (tcFn (pred n)))
      = eqc (predcT (tcFn (liftTerm k n))) (tcFn (pred (liftTerm k n))) :=
  ROBINSON_PlusPlus.Meta.EvalPredPrf.liftTerm_evalPredCode k n

/-! ### 4.4 · `pcc_pred_succ_code` (sondeo :1788) — es `EvalPredPrf.pcc_ax26_computed`
    instanciado en `w := tcFn m`. -/

theorem dup_pcc_pred_succ_code (m : Term) :
    Prf (provFromCode (eqCodeFn (predcT (succcT (tcFn m))) (tcFn m))) :=
  ROBINSON_PlusPlus.Meta.EvalPredPrf.pcc_ax26_computed (tcFn m)

/-! ### 4.5 · `psi_l1` (sondeo :1585) — es `StrongInductionPrf.psi_lift_form` instanciado.
    Hace falta `hPHI1`, que se prueba aqui abajo (es la unica prueba del fichero). -/

namespace SF

theorem liftF_targetSubsttc (k : Nat) (v s X : Term) :
    liftFormula k (targetSubsttc v s X)
      = targetSubsttc (liftTerm k v) (liftTerm k s) (liftTerm k X) := by
  simp only [targetSubsttc, liftFormula_provFromCode_open, eqc, substtcT, funcc, tcFn, substtc,
    cons, nil, zero, succ, liftTerm, liftTerms, liftTerm_strCode]

theorem liftF_targetSubsttsc (k : Nat) (v s X : Term) :
    liftFormula k (targetSubsttsc v s X)
      = targetSubsttsc (liftTerm k v) (liftTerm k s) (liftTerm k X) := by
  simp only [targetSubsttsc, liftFormula_provFromCode_open, eqc, substtscT, funcc, tcFn, substtsc,
    cons, nil, zero, succ, liftTerm, liftTerms, liftTerm_strCode]

theorem liftF_CONJ (k : Nat) (w v s X : Term) :
    liftFormula k (CONJ w v s X)
      = CONJ (liftTerm k w) (liftTerm k v) (liftTerm k s) (liftTerm k X) := by
  simp only [CONJ, land, liftFormula, liftF_isTC1, liftF_wfAll1, liftF_argsIn,
    liftF_targetSubsttc, liftF_targetSubsttsc]

theorem hPHI1 : liftFormula 1 PHI = PHI := by
  simp only [PHI, PHIbody, liftFormula, liftF_CONJ, liftTerm, Nat.reduceAdd, Nat.reduceLT,
    reduceIte]

end SF

theorem dup_psi_l1 : liftFormula 0 (PSI SF.PHI)
    = Formula.forall (Formula.impl (lt (.var 0) (.var 2)) SF.PHI) :=
  ROBINSON_PlusPlus.Meta.StrongInductionPrf.psi_lift_form SF.PHI SF.hPHI1

/-! ############################################################################
    ## §5 · SUBSUNCION — y va en la direccion CONTRARIA a la que teme el ADR-019
    ############################################################################

    Ningun lema del sondeo es MAS GENERAL que uno de produccion. Al reves: hay dos piezas de
    produccion que SUBSUMEN a piezas del sondeo, y una de ellas se lleva por delante el §13
    entero. -/

/-! ### 5.1 · `PredHyp` (sondeo §10, y todo su §13 para descargarla) esta SUBSUMIDA por
    `Meta/EvalPredPrf.lean` (`pcc_eval_pred`), que **no lleva la guarda `v < n`**. -/

theorem predHyp_de_produccion : SF.PredHyp := fun v n =>
  prf_deduction (prf_to_prfH (ROBINSON_PlusPlus.Meta.EvalPredPrf.pcc_eval_pred n) _)

/-- Y la version sin guarda, que es ESTRICTAMENTE mas fuerte, tambien esta ya. -/
theorem pred_dotado_sin_guarda (n : Term) :
    Prf (provFromCode (eqc (predcT (tcFn n)) (tcFn (pred n)))) :=
  ROBINSON_PlusPlus.Meta.EvalPredPrf.pcc_eval_pred n

/-! ### 5.2 · `PSI_inst` del sondeo (3 niveles, instanciado a `PHI`) contra el de produccion
    (1 nivel, GENERICO en `Φ`). El general que falta —a 3 niveles y generico— se prueba **solo
    con lo que hay al llegar a `Meta/StrongInductionPrf.lean`**; la comprobacion de imports
    aislados esta en `Probe/B3_substtc_dedup_STRONGIND.lean` (que recompila hoy). Aqui queda
    el enunciado, para poder citarlo. -/

theorem psi_lift_form3_general (Φ : Formula) (hΦ : liftFormula 1 Φ = Φ) :
    liftFormula 0 (liftFormula 0 (liftFormula 0 (PSI Φ)))
      = Formula.forall (Formula.impl (lt (.var 0) (.var 4)) Φ) := by
  rw [ROBINSON_PlusPlus.Meta.StrongInductionPrf.psi_lift_form Φ hΦ]
  simp only [lt, liftFormula, liftTerm, liftTerms, Nat.reduceAdd, Nat.reduceLT, reduceIte, hΦ]

theorem PSI_inst3_general (Φ : Formula) (hΦ : liftFormula 1 Φ = Φ) {Γ : List Formula}
    (hpsi : PrfH Γ (liftFormula 0 (liftFormula 0 (liftFormula 0 (PSI Φ))))) (z : Term) :
    PrfH Γ (Formula.impl (lt z (.var 3)) (substFormula 0 z Φ)) := by
  rw [psi_lift_form3_general Φ hΦ] at hpsi
  have h := PrfH_spec hpsi z
  have e : substFormula 0 z (Formula.impl (lt (.var 0) (.var 4)) Φ)
      = Formula.impl (lt z (.var 3)) (substFormula 0 z Φ) := by
    simp only [substFormula, lt, substTerm, substTerms, Nat.reduceEqDiff, Nat.reduceGT,
      Nat.reduceSub, reduceIte, if_true]
  rwa [e] at h

/-- Y el `PSI_inst` del sondeo es EXACTAMENTE ese general instanciado. -/
theorem sondeo_PSI_inst_es_el_general {Γ : List Formula} (hpsi : PrfH Γ SF.PSI3) (z : Term) :
    PrfH Γ (Formula.impl (lt z (.var 3)) (substFormula 0 z SF.PHI)) :=
  PSI_inst3_general SF.PHI SF.hPHI1 hpsi z

/-! ############################################################################
    ## §6 · POR QUE LAS COLISIONES SON UN PELIGRO **SILENCIOSO**
    ############################################################################ -/

/-! ### 6.1 · Ocho de los 17 homonimos estan YA EN LA RAIZ (`export` de `LiftcCodePrf`):
    `refl_caso_varc`, `refl_caso_funcc`, `refl_lista_nil`, `refl_lista_cons`,
    `refl_shapeUn_imp`, `refl_caso_funcc_imp`, `refl_shapeBin_imp`, `refl_lista_cons_imp`.
    El nombre PELADO, sin cualificar, resuelve HOY al de `liftc`. -/

example : Prf (ROBINSON_PlusPlus.Meta.LiftcCodePrf.targetLiftsc nil) := refl_lista_nil
example (X : Term) :
    Prf (Formula.impl (shapeUn X 0) (ROBINSON_PlusPlus.Meta.LiftcCodePrf.targetLift X)) :=
  refl_shapeUn_imp X

/-! ### 6.2 · El caso VERDADERAMENTE silencioso: `PHI` y `PHIbody` son `Formula`. Con un
    `open ROBINSON_PlusPlus.Meta.EvalLiftcPrf` mal puesto, un `PSI3` escrito con `PHI` pelado
    **compila igual** — y construye otra formula. El error no salta aqui, sino tres lemas
    despues. -/

section
open ROBINSON_PlusPlus.Meta.EvalLiftcPrf

/-- Escrito palabra por palabra como el `PSI3` del sondeo, pero con `PHI` resolviendo al
    de `liftc`. **Elabora sin una sola queja.** -/
def PSI3_MAL : Formula := liftFormula 0 (liftFormula 0 (liftFormula 0 (PSI PHI)))

end

/-- Y no es el mismo objeto. -/
example : True := by
  fail_if_success (have : PSI3_MAL = SF.PSI3 := rfl)
  trivial

/-! ### 6.3 · Contraste: el mismo `PSI3` escrito con el `PHI` correcto SI es el del sondeo. -/

theorem PSI3_BIEN : SF.PSI3 = liftFormula 0 (liftFormula 0 (liftFormula 0 (PSI SF.PHI))) := rfl


/-! ############################################################################
    ## §7 · MUERTOS — censo de consumidores REALES dentro del sondeo
    ############################################################################

    ⚠️ Esto es medida de SCRIPT (recorrido de las 156 declaraciones contando usos en el
    TEXTO DE CODIGO, con los comentarios `/- -/` y `--` borrados antes de contar), no del
    compilador: lo digo para que se audite como lo que es.

    **Sin ni un consumidor de CODIGO (16):**

    | nombre                    | :linea | por que |
    |---------------------------|-------:|---------|
    | `refl_caso_funcc`         |  859 | ⚠️ el ensamblaje usa `refl_caso_funcc_imp` (moneda OBJETO) |
    | `refl_lista_cons`         |  907 | ⚠️ idem, usa `refl_lista_cons_imp` |
    | `refl_caso_varc`          | 1090 | ⚠️ `refl_shapeUn_imp` llama a `refl_caso_varc_at`, no a este |
    | `substtcT_termCode`       |   55 | puente `:= rfl` de ADR-012 (documental) |
    | `substtscT_termCode`      |   57 | idem |
    | `varcT_termCode`          |   59 | idem — y ya esta en produccion |
    | `funccT_termCode`         |   60 | idem — y ya esta en produccion |
    | `predcT_termCode`         |   62 | idem — y ya esta en produccion |
    | `eqc_eq_eqCodeFn`         |   64 | duplicado (§4.1) |
    | `SUBSTTSC_NIL_BODY_ok`    |  232 | puente `:= rfl` (documental) |
    | `SUBSTTC_FUNC_BODY_ok`    |  267 | idem |
    | `SUBSTTSC_CONS_BODY_ok`   |  379 | idem |
    | `SUBSTTC_VAR_EQ_BODY_ok`  |  528 | idem |
    | `SUBSTTC_VAR_GT_BODY_ok`  |  529 | idem |
    | `SUBSTTC_VAR_LT_BODY_ok`  |  530 | idem |
    | `AX26_BODY_ok`            | 1785 | idem — y ya esta en produccion |

    (`shapeUn0_es_varc` :1112 y `shapeBin1_es_funcc` :1114 tampoco tienen consumidor, pero ya
    estan en produccion, luego no son candidatos a promover: son 18 en total sin consumidor.)

    Las tres primeras son **exactamente la trampa de `SubstfcPlanos`**: el `_imp` es lo que
    consume el ensamblaje, y la version con la hipotesis en moneda META se queda huerfana.
    Y son, ademas, tres de las 17 colisiones (§2.1, §2.3, §2.4): **no hay que renombrarlas,
    hay que NO promoverlas.**

    Los tres teoremas primados del final (`pcc_eval_substtc'` :1853, `pcc_eval_substtsc'`
    :1858, `pcc_eval_substtc_hasWit'` :1865) tampoco tienen consumidor DENTRO del sondeo:
    son la ENTREGA, no codigo muerto.

    Y `refl_lista_nil` (:899) **si** tiene consumidor —`PHI_step`—, asi que esa colision
    (§2.2) hay que resolverla renombrando. -/

/-! ############################################################################
    ## §8 · UNA CITA DE PRODUCCION QUE HOY YA ES FALSA
    ############################################################################

    `prf_substtc_termCode_closed` / `_numeralM` / `_zero` **SUBIERON hoy** de
    `Meta/LiftcCodePrf.lean` a `Meta/CodeCtorKit.lean` (rama B3). Cualquier puente que los cite
    como `LiftcCodePrf.…` —y hay uno en `Probe/B3_substtc_dedup.lean`, del angulo anterior—
    ya no elabora. Queda medido por los dos lados: -/

/-- El nombre YA NO EXISTE en `LiftcCodePrf`. -/
example : True := by
  fail_if_success (have := @ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_substtc_termCode_closed)
  trivial
example : True := by
  fail_if_success (have := @ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_substtc_termCode_numeralM)
  trivial
example : True := by
  fail_if_success (have := @ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_substtc_termCode_zero)
  trivial

/-- Y SI existe en `CodeCtorKit`, que es donde hay que citarlo. -/
theorem cita_buena_termCode_closed (v : Nat) (W t : Term) (ht : ∀ c : Nat, liftTerm c t = t) :
    Prf (substtc (numeral v) W (termCode t) =eq termCode t) :=
  ROBINSON_PlusPlus.Meta.CodeCtorKit.prf_substtc_termCode_closed v W t ht

end B3B

#print axioms B3B.ctl_pos
#print axioms B3B.no_colisiona_predcT_termCode
#print axioms B3B.no_colisiona_pcc_thm_inst4
#print axioms B3B.no_colisiona_pcc_axiom_inst4
#print axioms B3B.dup_eqc_por_symm
#print axioms B3B.dup_eqc_ya_esta
#print axioms B3B.dup_PrfH_congr_pred
#print axioms B3B.dup_liftT_predcode
#print axioms B3B.dup_pcc_pred_succ_code
#print axioms B3B.dup_psi_l1
#print axioms B3B.predHyp_de_produccion
#print axioms B3B.pred_dotado_sin_guarda
#print axioms B3B.psi_lift_form3_general
#print axioms B3B.PSI_inst3_general
#print axioms B3B.sondeo_PSI_inst_es_el_general
#print axioms B3B.PSI3_BIEN
#print axioms B3B.cita_buena_termCode_closed

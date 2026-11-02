/-
# EL DESCENSO — induccion FUERTE sobre el valor del codigo.

Objetivo:  `DESCENSO : ∀ w s, Prf (isTC1 w s) → Prf (targetLift s)`.

Fichero AUTOCONTENIDO (`import ROBINSON_PlusPlus.Meta`). Las piezas van COPIADAS de
`sondeos/ReflectorDesdeConsumidor.lean`, `sondeos/ClausuraLiftSinWTs.lean` y
`sondeos/DiscriminaEcuacional.lean`.

    lake env lean Probe/Desc_fuerte.lean

## FASE 0 — EL GATE:  `liftFormula 1 Φ = Φ`
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
open ROBINSON_PlusPlus.Meta.ChainPrf ROBINSON_PlusPlus.Meta.ChainOkBoundedPrf
open ROBINSON_PlusPlus.Meta.TrackedCorePrf ROBINSON_PlusPlus.Meta.Delta0ReflectPrf
open ROBINSON_PlusPlus.Meta.NatOrderPrf ROBINSON_PlusPlus.Meta.CantorMonoPrf
open ROBINSON_PlusPlus.Meta.StrongInductionPrf ROBINSON_PlusPlus.Meta.NumListPrf

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

namespace DescFuerte

/-! ## §1 · Los constructores de codigo (copia de `ReflectorDesdeConsumidor` §1) -/

def liftcT (c t : Term) : Term := funcc (strCode "liftc") (cons c (cons t nil))
def liftscT (c ts : Term) : Term := funcc (strCode "liftsc") (cons c (cons ts nil))

def targetLift (s : Term) : Formula :=
  provFromCode (eqc (liftcT (termCode zero) (tcFn s)) (tcFn (liftc zero s)))
def targetLiftsc (b : Term) : Formula :=
  provFromCode (eqc (liftscT (termCode zero) (tcFn b)) (tcFn (liftsc zero b)))

/-! ## §2 · El predicado sin `wTs` (copia de `ClausuraLiftSinWTs` §1) -/

def argsInBody (wT Y : Term) : Formula :=
  Formula.impl (lt (.var 0) (liftTerm 0 (lenc Y)))
    (In (nthc (liftTerm 0 Y) (.var 0)) (liftTerm 0 wT))
def argsIn (wT Y : Term) : Formula := Formula.forall (argsInBody wT Y)

def shapeUn (X : Term) (k : Nat) : Formula :=
  Formula.eq X (cons (numeralM k) (cons (nthc X (numeralM 1)) nil))
def shapeBin (X : Term) (k : Nat) : Formula :=
  Formula.eq X (cons (numeralM k)
    (cons (nthc X (numeralM 1)) (cons (nthc X (numeralM 2)) nil)))

def isTermCodeE1 (wT X : Term) : Formula :=
  lor (shapeUn X 0) (land (shapeBin X 1) (argsIn wT (nthc X (numeralM 2))))

def wfAll1Body (w : Term) : Formula :=
  Formula.impl (lt (.var 0) (liftTerm 0 (lenc w)))
    (isTermCodeE1 (liftTerm 0 w) (nthc (liftTerm 0 w) (.var 0)))
def wfAll1 (w : Term) : Formula := Formula.forall (wfAll1Body w)

def isTC1 (w c : Term) : Formula := land (wfAll1 w) (In c w)

/-! ## §3 · `substTerm` sobre `termCode` (copia de `ReflectorDesdeConsumidor` §9) -/

mutual
theorem substTerm_termCode (v : Nat) (u : Term) :
    ∀ t : Term, substTerm v u (termCode t) = termCode t
  | .var _ => by simp only [termCode, cons, nil, zero, substTerm, substTerms, substTerm_numeral]
  | .func s ts => by
      simp only [termCode, cons, nil, zero, substTerm, substTerms, substTerm_numeral,
        substTerm_strCode, substTerm_termsCode v u ts]
theorem substTerm_termsCode (v : Nat) (u : Term) :
    ∀ ts : List Term, substTerm v u (termsCode ts) = termsCode ts
  | []      => rfl
  | t :: ts => by
      simp only [termsCode, cons, substTerm, substTerms, substTerm_termCode v u t,
        substTerm_termsCode v u ts]
end

/-! ## §4 · `liftFormula`/`substFormula` atraviesan las cinco piezas -/

theorem liftF_targetLift (k : Nat) (s : Term) :
    liftFormula k (targetLift s) = targetLift (liftTerm k s) := by
  simp only [targetLift, liftFormula_provFromCode_open, eqc, liftcT, funcc, tcFn, liftc,
    cons, nil, zero, succ, liftTerm, liftTerms, liftTerm_termCode, liftTerm_strCode]

theorem substF_targetLift (v : Nat) (u s : Term) :
    substFormula v u (targetLift s) = targetLift (substTerm v u s) := by
  simp only [targetLift, substFormula_provFromCode_open, eqc, liftcT, funcc, tcFn, liftc,
    cons, nil, zero, succ, substTerm, substTerms, substTerm_termCode, substTerm_strCode]

theorem liftF_targetLiftsc (k : Nat) (s : Term) :
    liftFormula k (targetLiftsc s) = targetLiftsc (liftTerm k s) := by
  simp only [targetLiftsc, liftFormula_provFromCode_open, eqc, liftscT, funcc, tcFn, liftsc,
    cons, nil, zero, succ, liftTerm, liftTerms, liftTerm_termCode, liftTerm_strCode]

theorem substF_targetLiftsc (v : Nat) (u s : Term) :
    substFormula v u (targetLiftsc s) = targetLiftsc (substTerm v u s) := by
  simp only [targetLiftsc, substFormula_provFromCode_open, eqc, liftscT, funcc, tcFn, liftsc,
    cons, nil, zero, succ, substTerm, substTerms, substTerm_termCode, substTerm_strCode]

theorem liftF_argsIn (k : Nat) (wT Y : Term) :
    liftFormula k (argsIn wT Y) = argsIn (liftTerm k wT) (liftTerm k Y) := by
  simp only [argsIn, argsInBody, liftFormula, lt, lenc, nthc, In, liftTerm, liftTerms,
    Nat.zero_lt_succ, reduceIte, if_true, ← FOL.liftTerm_comm_zero]

theorem substF_argsIn (v : Nat) (s wT Y : Term) :
    substFormula v s (argsIn wT Y) = argsIn (substTerm v s wT) (substTerm v s Y) := by
  have hz : (0 = v + 1) = False := eq_false (by omega)
  have hz2 : (0 > v + 1) = False := eq_false (by omega)
  simp only [argsIn, argsInBody, substFormula, substTerm, substTerms, lt, lenc, nthc, In,
    liftTerm, liftTerms, hz, hz2, if_false, Nat.zero_lt_succ, reduceIte, if_true,
    FOL.substTerm_lift_comm_zero]

theorem substF_isTermCodeE1 (v : Nat) (s wT X : Term) :
    substFormula v s (isTermCodeE1 wT X)
      = isTermCodeE1 (substTerm v s wT) (substTerm v s X) := by
  simp only [isTermCodeE1, shapeUn, shapeBin, lor, land, substFormula, substF_argsIn,
    nthc, cons, nil, zero, substTerm, substTerms, substTerm_numeralM]

theorem liftF_isTermCodeE1 (k : Nat) (wT X : Term) :
    liftFormula k (isTermCodeE1 wT X)
      = isTermCodeE1 (liftTerm k wT) (liftTerm k X) := by
  simp only [isTermCodeE1, shapeUn, shapeBin, lor, land, liftFormula, liftF_argsIn,
    nthc, cons, nil, zero, liftTerm, liftTerms, liftTerm_numeralM]

theorem liftF_wfAll1 (k : Nat) (w : Term) :
    liftFormula k (wfAll1 w) = wfAll1 (liftTerm k w) := by
  simp only [wfAll1, wfAll1Body, liftFormula, liftF_isTermCodeE1, lt, lenc, nthc,
    liftTerm, liftTerms, Nat.zero_lt_succ, reduceIte, if_true, ← FOL.liftTerm_comm_zero]

theorem substF_wfAll1 (v : Nat) (s w : Term) :
    substFormula v s (wfAll1 w) = wfAll1 (substTerm v s w) := by
  have hz : (0 = v + 1) = False := eq_false (by omega)
  have hz2 : (0 > v + 1) = False := eq_false (by omega)
  simp only [wfAll1, wfAll1Body, substFormula, substF_isTermCodeE1, lt, lenc, nthc,
    substTerm, substTerms, liftTerm, liftTerms, hz, hz2, if_false, Nat.zero_lt_succ,
    reduceIte, if_true, FOL.substTerm_lift_comm_zero]

theorem liftF_isTC1 (k : Nat) (w c : Term) :
    liftFormula k (isTC1 w c) = isTC1 (liftTerm k w) (liftTerm k c) := by
  simp only [isTC1, land, liftFormula, liftF_wfAll1, In, liftTerm, liftTerms]

theorem substF_isTC1 (v : Nat) (s w c : Term) :
    substFormula v s (isTC1 w c) = isTC1 (substTerm v s w) (substTerm v s c) := by
  simp only [isTC1, land, substFormula, substF_wfAll1, In, substTerm, substTerms]

/-! ## §5 · EL MOTIVO DE LA INDUCCION FUERTE — `w` va DENTRO -/

/-- El cuerpo: las DOS mitades (nodo y lista de argumentos) contra el MISMO testigo. -/
def bodyF (W X : Term) : Formula :=
  land (Formula.impl (isTC1 W X) (targetLift X))
       (Formula.impl (land (wfAll1 W) (argsIn W X)) (targetLiftsc X))

theorem liftF_bodyF (k : Nat) (W X : Term) :
    liftFormula k (bodyF W X) = bodyF (liftTerm k W) (liftTerm k X) := by
  simp only [bodyF, land, liftFormula, liftF_isTC1, liftF_targetLift, liftF_wfAll1,
    liftF_argsIn, liftF_targetLiftsc]

theorem substF_bodyF (v : Nat) (s W X : Term) :
    substFormula v s (bodyF W X) = bodyF (substTerm v s W) (substTerm v s X) := by
  simp only [bodyF, land, substFormula, substF_isTC1, substF_targetLift, substF_wfAll1,
    substF_argsIn, substF_targetLiftsc]

/-- **EL MOTIVO.** `#0` es el codigo sobre el que se induce; el testigo `w` va CUANTIFICADO
    DENTRO (es `#0` bajo el binder, y el codigo pasa a ser `#1`). -/
def PHI : Formula := Formula.forall (bodyF (.var 0) (.var 1))

/-- **EL GATE**: `liftFormula 1 Φ = Φ` — lo que exige `prf_strong_induction`. -/
theorem hPHI : liftFormula 1 PHI = PHI := by
  simp only [PHI, liftFormula, liftF_bodyF, liftTerm, Nat.zero_lt_succ, Nat.reduceAdd,
    Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceSub, reduceIte]

/-- `Φ[t]` es el cuerpo con el codigo `t` y el testigo aun cuantificado. -/
theorem PHI_at (t : Term) : substFormula 0 t PHI = Formula.forall (bodyF (.var 0) (liftTerm 0 t)) := by
  simp only [PHI, substFormula, substF_bodyF, substTerm, FOL.substTerm_liftTerm,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceSub, reduceIte,
    if_true]

/-- Instanciacion completa: `Φ[X]` con el testigo en `W`. -/
theorem PHI_inst (X W : Term) (h : Prf (substFormula 0 X PHI)) : Prf (bodyF W X) := by
  rw [PHI_at] at h
  have h2 := prf_spec h W
  rwa [substF_bodyF, FOL.substTerm_liftTerm] at h2

/-! ## §6 · COPIA LITERAL de sondeos/ReflectorDesdeConsumidor.lean §1(resto),§3-§7,§9 -/
/-- `varc x = cons 0 (cons x nil)` ⇒ su imagen punteada es el `unT 0` del KIT. CERO simbolos
    nuevos. -/
def varcT (X : Term) : Term := unT 0 X
/-- `funcc a b = cons 1 (cons a (cons b nil))` ⇒ su imagen punteada es el `binT 1` del KIT. -/
def funccT (X Y : Term) : Term := binT 1 X Y

theorem liftcT_termCode (c t : Term) :
    liftcT (termCode c) (termCode t) = termCode (liftc c t) := rfl
theorem liftscT_termCode (c t : Term) :
    liftscT (termCode c) (termCode t) = termCode (liftsc c t) := rfl
theorem varcT_termCode (x : Term) : varcT (termCode x) = termCode (varc x) := rfl
theorem funccT_termCode (x y : Term) : funccT (termCode x) (termCode y) = termCode (funcc x y) :=
  rfl

/-- `eqc` y `eqCodeFn` son EL MISMO constructor. -/
theorem eqc_eq_eqCodeFn (a b : Term) : eqc a b = eqCodeFn a b := rfl

/-! ## §3 · Fontaneria: congruencias e invariancias de los constructores nuevos -/

theorem prf_congr_liftcT {c c' t t' : Term} (hc : Prf (c =eq c')) (ht : Prf (t =eq t')) :
    Prf (liftcT c t =eq liftcT c' t') :=
  prf_congr_funcc2 (prf_eq_trans (prf_congr_cons_head hc)
    (prf_congr_cons_tail (prf_congr_cons_head ht)))

theorem prf_congr_liftscT {c c' t t' : Term} (hc : Prf (c =eq c')) (ht : Prf (t =eq t')) :
    Prf (liftscT c t =eq liftscT c' t') :=
  prf_congr_funcc2 (prf_eq_trans (prf_congr_cons_head hc)
    (prf_congr_cons_tail (prf_congr_cons_head ht)))

theorem prf_congr_varcT {X X' : Term} (h : Prf (X =eq X')) : Prf (varcT X =eq varcT X') :=
  prf_congr_unT h
theorem prf_congr_funccT {X X' Y Y' : Term} (hx : Prf (X =eq X')) (hy : Prf (Y =eq Y')) :
    Prf (funccT X Y =eq funccT X' Y') := prf_congr_binT hx hy

theorem prf_substtc_liftcT (v W x y : Term) :
    Prf (substtc v W (liftcT x y) =eq liftcT (substtc v W x) (substtc v W y)) :=
  prf_substtc_funcc2 v W (strCode "liftc") x y
theorem prf_substtc_liftscT (v W x y : Term) :
    Prf (substtc v W (liftscT x y) =eq liftscT (substtc v W x) (substtc v W y)) :=
  prf_substtc_funcc2 v W (strCode "liftsc") x y

theorem substtc_inv_liftcT {X Y : Term}
    (hX : ∀ W, Prf (substtc zero W X =eq X)) (hY : ∀ W, Prf (substtc zero W Y =eq Y)) :
    ∀ W, Prf (substtc zero W (liftcT X Y) =eq liftcT X Y) := fun W =>
  prf_eq_trans (prf_substtc_liftcT zero W X Y) (prf_congr_liftcT (hX W) (hY W))
theorem substtc_inv_liftscT {X Y : Term}
    (hX : ∀ W, Prf (substtc zero W X =eq X)) (hY : ∀ W, Prf (substtc zero W Y =eq Y)) :
    ∀ W, Prf (substtc zero W (liftscT X Y) =eq liftscT X Y) := fun W =>
  prf_eq_trans (prf_substtc_liftscT zero W X Y) (prf_congr_liftscT (hX W) (hY W))

/-! ### `substtc` a NIVEL ARBITRARIO sobre los codigos cerrados (copia de Paso2 §2) -/

theorem prf_substtc_termCode_closed (v : Nat) (W t : Term) (ht : ∀ c : Nat, liftTerm c t = t) :
    Prf (substtc (numeral v) W (termCode t) =eq termCode t) := by
  have h := prf_substtc_arith_open v W t
  rwa [substCodeT_closed v W t ht] at h

theorem prf_substtc_termCode_numeralM (v m : Nat) (W : Term) :
    Prf (substtc (numeral v) W (termCode (numeralM m)) =eq termCode (numeralM m)) :=
  prf_substtc_termCode_closed v W (numeralM m) (fun c => liftTerm_numeralM c m)

theorem prf_substtc_termCode_zero (v : Nat) (W : Term) :
    Prf (substtc (numeral v) W (termCode zero) =eq termCode zero) :=
  prf_substtc_termCode_closed v W zero (fun _ => rfl)

theorem prf_substtc_unT_at (m v : Nat) (W a : Term) :
    Prf (substtc (numeral v) W (unT m a) =eq unT m (substtc (numeral v) W a)) := by
  unfold unT consT
  refine prf_eq_trans (prf_substtc_funcc2 _ _ _ _ _) ?_
  refine prf_congr_funcc2 ?_
  refine prf_eq_trans (prf_congr_cons_head (prf_substtc_termCode_numeralM v m W)) ?_
  refine prf_congr_cons_tail (prf_congr_cons_head ?_)
  refine prf_eq_trans (prf_substtc_funcc2 _ _ _ _ _) ?_
  exact prf_congr_funcc2
    (prf_congr_cons_tail (prf_congr_cons_head (prf_substtc_termCode_zero v W)))

theorem prf_substtc_binT_at (m v : Nat) (W a b : Term) :
    Prf (substtc (numeral v) W (binT m a b)
      =eq binT m (substtc (numeral v) W a) (substtc (numeral v) W b)) := by
  unfold binT consT
  refine prf_eq_trans (prf_substtc_funcc2 _ _ _ _ _) ?_
  refine prf_congr_funcc2 ?_
  refine prf_eq_trans (prf_congr_cons_head (prf_substtc_termCode_numeralM v m W)) ?_
  refine prf_congr_cons_tail (prf_congr_cons_head ?_)
  refine prf_eq_trans (prf_substtc_funcc2 _ _ _ _ _) ?_
  refine prf_congr_funcc2 ?_
  refine prf_congr_cons_tail (prf_congr_cons_head ?_)
  refine prf_eq_trans (prf_substtc_funcc2 _ _ _ _ _) ?_
  exact prf_congr_funcc2
    (prf_congr_cons_tail (prf_congr_cons_head (prf_substtc_termCode_zero v W)))

theorem prf_substtc_varcT_at (v : Nat) (W a : Term) :
    Prf (substtc (numeral v) W (varcT a) =eq varcT (substtc (numeral v) W a)) :=
  prf_substtc_unT_at 0 v W a
theorem prf_substtc_funccT_at (v : Nat) (W a b : Term) :
    Prf (substtc (numeral v) W (funccT a b)
      =eq funccT (substtc (numeral v) W a) (substtc (numeral v) W b)) :=
  prf_substtc_binT_at 1 v W a b

/-! ## §4 · LAS ECUACIONES DE `liftc`/`liftsc`, DOTADAS

    Las cinco ecuaciones recursivas de `liftc`/`liftsc` (`ax_liftc_var_lt`, `ax_liftc_var_ge`,
    `ax_liftc_func`, `ax_liftsc_nil`, `ax_liftsc_cons`) son `forall_2`/`forall_3`/`forall_`.
    Su imagen DOTADA sale por `pcc_axiom_inst*` + computo del `substfc` sobre el codigo
    explicito (patron `pcc_nthc_zero_code`, `pcc_substfc_forall_dot`).

    ⚠️ MEDIDA CENTRAL DE ESTE FICHERO: **todas son LIBRES DE CUANTIFICADOR**. Ni un solo
    `bdAllCode` aparece aqui. -/

def LIFTC_FUNC_BODY : Formula :=
  liftc (.var 2) (funcc (.var 1) (.var 0)) =eq funcc (.var 1) (liftsc (.var 2) (.var 0))

theorem LIFTC_FUNC_BODY_ok : ax_liftc_func = forall_3 LIFTC_FUNC_BODY := rfl

/-- **`ax_liftc_func` DOTADA**: `⊢ Prov(⌜ liftc(ċ, funcc(ȧ,ḃ)) = funcc(ȧ, liftsc(ċ,ḃ)) ⌝)`,
    con `c`, `a`, `b` **ABSTRACTOS**. -/
theorem pcc_liftc_func_code (c a b : Term) :
    Prf (provFromCode (eqCodeFn
      (liftcT (tcFn c) (funccT (tcFn a) (tcFn b)))
      (funccT (tcFn a) (liftscT (tcFn c) (tcFn b))))) := by
  let W2 : Term := liftc zero (liftc zero (tcFn c))
  let W1 : Term := liftc zero (tcFn a)
  let W0 : Term := tcFn b
  have hin : Prf (substfc (succ (succ zero)) W2 (formCode LIFTC_FUNC_BODY)
      =eq eqCodeFn (liftcT W2 (funccT (varc (numeral 1)) (varc (numeral 0))))
                   (funccT (varc (numeral 1)) (liftscT W2 (varc (numeral 0))))) :=
    prf_substfc_arith_open 2 W2 LIFTC_FUNC_BODY
  have hA2 : Prf (W2 =eq tcFn c) :=
    prf_eq_trans (prf_congr_liftc (prf_liftc_tcFn c)) (prf_liftc_tcFn c)
  have hnorm : Prf (eqCodeFn (liftcT W2 (funccT (varc (numeral 1)) (varc (numeral 0))))
                   (funccT (varc (numeral 1)) (liftscT W2 (varc (numeral 0))))
      =eq eqCodeFn (liftcT (tcFn c) (funccT (varc (numeral 1)) (varc (numeral 0))))
                   (funccT (varc (numeral 1)) (liftscT (tcFn c) (varc (numeral 0))))) :=
    prf_congr_eqCodeFn (prf_congr_liftcT hA2 (prf_refl _))
      (prf_congr_funccT (prf_refl _) (prf_congr_liftscT hA2 (prf_refl _)))
  have hv1 : Prf (substtc (succ zero) W1 (varc (numeral 1)) =eq tcFn a) :=
    prf_eq_trans (prf_mp (prf_substtc_var_eq (succ zero) W1 (numeral 1)) (prf_refl _))
      (prf_liftc_tcFn a)
  have hv0 : Prf (substtc (succ zero) W1 (varc (numeral 0)) =eq varc (numeral 0)) :=
    prf_mp (prf_substtc_var_lt (succ zero) W1 (numeral 0)) (prf_zero_lt_succ zero)
  have hc1 : Prf (substtc (succ zero) W1 (tcFn c) =eq tcFn c) := prf_substtc_tcFn_at 1 W1 c
  have hmid : Prf (substfc (succ zero) W1 (eqCodeFn
        (liftcT (tcFn c) (funccT (varc (numeral 1)) (varc (numeral 0))))
        (funccT (varc (numeral 1)) (liftscT (tcFn c) (varc (numeral 0)))))
      =eq eqCodeFn (liftcT (tcFn c) (funccT (tcFn a) (varc (numeral 0))))
                   (funccT (tcFn a) (liftscT (tcFn c) (varc (numeral 0))))) := by
    refine prf_eq_trans (prf_substfc_eq (succ zero) W1 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_liftcT (succ zero) W1 _ _) ?_
      refine prf_congr_liftcT hc1 ?_
      exact prf_eq_trans (prf_substtc_funccT_at 1 W1 _ _) (prf_congr_funccT hv1 hv0)
    · refine prf_eq_trans (prf_substtc_funccT_at 1 W1 _ _) ?_
      refine prf_congr_funccT hv1 ?_
      exact prf_eq_trans (prf_substtc_liftscT (succ zero) W1 _ _) (prf_congr_liftscT hc1 hv0)
  have hout : Prf (substfc zero W0 (eqCodeFn
        (liftcT (tcFn c) (funccT (tcFn a) (varc (numeral 0))))
        (funccT (tcFn a) (liftscT (tcFn c) (varc (numeral 0)))))
      =eq eqCodeFn (liftcT (tcFn c) (funccT (tcFn a) (tcFn b)))
                   (funccT (tcFn a) (liftscT (tcFn c) (tcFn b)))) := by
    refine prf_eq_trans (prf_substfc_eq zero W0 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_liftcT zero W0 _ _) ?_
      refine prf_congr_liftcT (prf_substtc_tcFn W0 c) ?_
      exact prf_eq_trans (prf_substtc_funccT_at 0 W0 _ _)
        (prf_congr_funccT (prf_substtc_tcFn W0 a) (prf_substtc_varc0 W0))
    · refine prf_eq_trans (prf_substtc_funccT_at 0 W0 _ _) ?_
      refine prf_congr_funccT (prf_substtc_tcFn W0 a) ?_
      exact prf_eq_trans (prf_substtc_liftscT zero W0 _ _)
        (prf_congr_liftscT (prf_substtc_tcFn W0 c) (prf_substtc_varc0 W0))
  have hchain : Prf (substfc zero W0 (substfc (succ zero) W1
      (substfc (succ (succ zero)) W2 (formCode LIFTC_FUNC_BODY)))
      =eq eqCodeFn (liftcT (tcFn c) (funccT (tcFn a) (tcFn b)))
                   (funccT (tcFn a) (liftscT (tcFn c) (tcFn b)))) :=
    prf_eq_trans (prf_congr_substfc_arg3
      (prf_eq_trans (prf_congr_substfc_arg3 (prf_eq_trans hin hnorm)) hmid)) hout
  exact prf_mp (prf_provCode_congr hchain)
    (pcc_axiom_inst3 LIFTC_FUNC_BODY (show ax_liftc_func ∈ axioms by simp [axioms])
      (tcFn c) (tcFn a) (tcFn b))

/-- `substfc` atraviesa un atomo binario de codigo. -/
theorem prf_substfc_atom2CodeFn (v t : Term) (s : String) (a b : Term) :
    Prf (substfc v t (atom2CodeFn s a b)
      =eq atom2CodeFn s (substtc v t a) (substtc v t b)) := by
  unfold atom2CodeFn
  refine prf_eq_trans (prf_substfc_atom v t (strCode s) (cons a (cons b nil))) ?_
  refine prf_congr_cons_tail (prf_congr_cons_tail (prf_congr_cons_head ?_))
  refine prf_eq_trans (prf_substtsc_cons v t a (cons b nil)) ?_
  exact prf_congr_cons_tail
    (prf_eq_trans (prf_substtsc_cons v t b nil) (prf_congr_cons_tail (prf_substtsc_nil v t)))

theorem prf_substfc_ltCodeFn' (v t a b : Term) :
    Prf (substfc v t (ltCodeFn a b) =eq ltCodeFn (substtc v t a) (substtc v t b)) :=
  prf_substfc_atom2CodeFn v t lt_sym a b

def LIFTC_VARGE_BODY : Formula :=
  Formula.impl (lt (.var 1) (succ (.var 0)))
    (liftc (.var 1) (varc (.var 0)) =eq varc (succ (.var 0)))

theorem LIFTC_VARGE_BODY_ok : ax_liftc_var_ge = forall_2 LIFTC_VARGE_BODY := rfl

/-- **`ax_liftc_var_ge` DOTADA** (con la guarda interna `ċ < σṅ` SIN descargar). -/
theorem pcc_liftc_var_ge_code (c n : Term) :
    Prf (provFromCode (implc (ltCodeFn (tcFn c) (succcT (tcFn n)))
      (eqCodeFn (liftcT (tcFn c) (varcT (tcFn n))) (varcT (succcT (tcFn n)))))) := by
  let W1 : Term := liftc zero (tcFn c)
  let W0 : Term := tcFn n
  have hin : Prf (substfc (succ zero) W1 (formCode LIFTC_VARGE_BODY)
      =eq implc (ltCodeFn W1 (succcT (varc (numeral 0))))
            (eqCodeFn (liftcT W1 (varcT (varc (numeral 0))))
              (varcT (succcT (varc (numeral 0)))))) :=
    prf_substfc_arith_open 1 W1 LIFTC_VARGE_BODY
  have hA1 : Prf (W1 =eq tcFn c) := prf_liftc_tcFn c
  have hnorm : Prf (implc (ltCodeFn W1 (succcT (varc (numeral 0))))
        (eqCodeFn (liftcT W1 (varcT (varc (numeral 0))))
          (varcT (succcT (varc (numeral 0)))))
      =eq implc (ltCodeFn (tcFn c) (succcT (varc (numeral 0))))
            (eqCodeFn (liftcT (tcFn c) (varcT (varc (numeral 0))))
              (varcT (succcT (varc (numeral 0)))))) :=
    prf_congr_implc (prf_congr_atom2CodeFn hA1 (prf_refl _))
      (prf_congr_eqCodeFn (prf_congr_liftcT hA1 (prf_refl _)) (prf_refl _))
  have hout : Prf (substfc zero W0 (implc (ltCodeFn (tcFn c) (succcT (varc (numeral 0))))
        (eqCodeFn (liftcT (tcFn c) (varcT (varc (numeral 0))))
          (varcT (succcT (varc (numeral 0))))))
      =eq implc (ltCodeFn (tcFn c) (succcT (tcFn n)))
            (eqCodeFn (liftcT (tcFn c) (varcT (tcFn n))) (varcT (succcT (tcFn n))))) := by
    refine prf_eq_trans (prf_substfc_impl zero W0 _ _) ?_
    refine prf_congr_implc ?_ ?_
    · refine prf_eq_trans (prf_substfc_ltCodeFn' zero W0 _ _) ?_
      refine prf_congr_atom2CodeFn (prf_substtc_tcFn W0 c) ?_
      exact prf_eq_trans (prf_substtc_funcc1 zero W0 _ _)
        (prf_congr_succcT (prf_substtc_varc0 W0))
    · refine prf_eq_trans (prf_substfc_eq zero W0 _ _) ?_
      refine prf_congr_eqCodeFn ?_ ?_
      · refine prf_eq_trans (prf_substtc_liftcT zero W0 _ _) ?_
        exact prf_congr_liftcT (prf_substtc_tcFn W0 c)
          (prf_eq_trans (prf_substtc_varcT_at 0 W0 _) (prf_congr_varcT (prf_substtc_varc0 W0)))
      · refine prf_eq_trans (prf_substtc_varcT_at 0 W0 _) ?_
        refine prf_congr_varcT ?_
        exact prf_eq_trans (prf_substtc_funcc1 zero W0 _ _)
          (prf_congr_succcT (prf_substtc_varc0 W0))
  have hchain : Prf (substfc zero W0 (substfc (succ zero) W1 (formCode LIFTC_VARGE_BODY))
      =eq implc (ltCodeFn (tcFn c) (succcT (tcFn n)))
            (eqCodeFn (liftcT (tcFn c) (varcT (tcFn n))) (varcT (succcT (tcFn n))))) :=
    prf_eq_trans (prf_congr_substfc_arg3 (prf_eq_trans hin hnorm)) hout
  exact prf_mp (prf_provCode_congr hchain)
    (pcc_axiom_inst2 LIFTC_VARGE_BODY (show ax_liftc_var_ge ∈ axioms by simp [axioms])
      (tcFn c) (tcFn n))

def LIFTSC_NIL_BODY : Formula := liftsc (.var 0) nil =eq nil

theorem LIFTSC_NIL_BODY_ok : ax_liftsc_nil = Formula.forall LIFTSC_NIL_BODY := rfl

/-- **`ax_liftsc_nil` DOTADA**. -/
theorem pcc_liftsc_nil_code (c : Term) :
    Prf (provFromCode (eqCodeFn (liftscT (tcFn c) (termCode nil)) (termCode nil))) := by
  have hin : Prf (substfc zero (tcFn c) (formCode LIFTSC_NIL_BODY)
      =eq eqCodeFn (liftscT (tcFn c) (termCode nil)) (termCode nil)) :=
    prf_substfc_arith_open 0 (tcFn c) LIFTSC_NIL_BODY
  exact prf_mp (prf_provCode_congr hin)
    (pcc_axiom_inst LIFTSC_NIL_BODY (show ax_liftsc_nil ∈ axioms by simp [axioms]) (tcFn c))

def LIFTSC_CONS_BODY : Formula :=
  liftsc (.var 2) (cons (.var 1) (.var 0))
    =eq cons (liftc (.var 2) (.var 1)) (liftsc (.var 2) (.var 0))

theorem LIFTSC_CONS_BODY_ok : ax_liftsc_cons = forall_3 LIFTSC_CONS_BODY := rfl

/-- **`ax_liftsc_cons` DOTADA**, con `c`, `h`, `t` **ABSTRACTOS**. -/
theorem pcc_liftsc_cons_code (c h t : Term) :
    Prf (provFromCode (eqCodeFn
      (liftscT (tcFn c) (consT (tcFn h) (tcFn t)))
      (consT (liftcT (tcFn c) (tcFn h)) (liftscT (tcFn c) (tcFn t))))) := by
  let W2 : Term := liftc zero (liftc zero (tcFn c))
  let W1 : Term := liftc zero (tcFn h)
  let W0 : Term := tcFn t
  have hin : Prf (substfc (succ (succ zero)) W2 (formCode LIFTSC_CONS_BODY)
      =eq eqCodeFn (liftscT W2 (consT (varc (numeral 1)) (varc (numeral 0))))
            (consT (liftcT W2 (varc (numeral 1))) (liftscT W2 (varc (numeral 0))))) :=
    prf_substfc_arith_open 2 W2 LIFTSC_CONS_BODY
  have hA2 : Prf (W2 =eq tcFn c) :=
    prf_eq_trans (prf_congr_liftc (prf_liftc_tcFn c)) (prf_liftc_tcFn c)
  have hnorm : Prf (eqCodeFn (liftscT W2 (consT (varc (numeral 1)) (varc (numeral 0))))
            (consT (liftcT W2 (varc (numeral 1))) (liftscT W2 (varc (numeral 0))))
      =eq eqCodeFn (liftscT (tcFn c) (consT (varc (numeral 1)) (varc (numeral 0))))
            (consT (liftcT (tcFn c) (varc (numeral 1)))
              (liftscT (tcFn c) (varc (numeral 0))))) :=
    prf_congr_eqCodeFn (prf_congr_liftscT hA2 (prf_refl _))
      (prf_congr_consT (prf_congr_liftcT hA2 (prf_refl _))
        (prf_congr_liftscT hA2 (prf_refl _)))
  have hv1 : Prf (substtc (succ zero) W1 (varc (numeral 1)) =eq tcFn h) :=
    prf_eq_trans (prf_mp (prf_substtc_var_eq (succ zero) W1 (numeral 1)) (prf_refl _))
      (prf_liftc_tcFn h)
  have hv0 : Prf (substtc (succ zero) W1 (varc (numeral 0)) =eq varc (numeral 0)) :=
    prf_mp (prf_substtc_var_lt (succ zero) W1 (numeral 0)) (prf_zero_lt_succ zero)
  have hc1 : Prf (substtc (succ zero) W1 (tcFn c) =eq tcFn c) := prf_substtc_tcFn_at 1 W1 c
  have hmid : Prf (substfc (succ zero) W1 (eqCodeFn
        (liftscT (tcFn c) (consT (varc (numeral 1)) (varc (numeral 0))))
        (consT (liftcT (tcFn c) (varc (numeral 1))) (liftscT (tcFn c) (varc (numeral 0)))))
      =eq eqCodeFn (liftscT (tcFn c) (consT (tcFn h) (varc (numeral 0))))
            (consT (liftcT (tcFn c) (tcFn h)) (liftscT (tcFn c) (varc (numeral 0))))) := by
    refine prf_eq_trans (prf_substfc_eq (succ zero) W1 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_liftscT (succ zero) W1 _ _) ?_
      refine prf_congr_liftscT hc1 ?_
      exact prf_eq_trans (prf_substtc_consT (succ zero) W1 _ _) (prf_congr_consT hv1 hv0)
    · refine prf_eq_trans (prf_substtc_consT (succ zero) W1 _ _) ?_
      refine prf_congr_consT ?_ ?_
      · exact prf_eq_trans (prf_substtc_liftcT (succ zero) W1 _ _) (prf_congr_liftcT hc1 hv1)
      · exact prf_eq_trans (prf_substtc_liftscT (succ zero) W1 _ _) (prf_congr_liftscT hc1 hv0)
  have hout : Prf (substfc zero W0 (eqCodeFn
        (liftscT (tcFn c) (consT (tcFn h) (varc (numeral 0))))
        (consT (liftcT (tcFn c) (tcFn h)) (liftscT (tcFn c) (varc (numeral 0)))))
      =eq eqCodeFn (liftscT (tcFn c) (consT (tcFn h) (tcFn t)))
            (consT (liftcT (tcFn c) (tcFn h)) (liftscT (tcFn c) (tcFn t)))) := by
    refine prf_eq_trans (prf_substfc_eq zero W0 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_liftscT zero W0 _ _) ?_
      refine prf_congr_liftscT (prf_substtc_tcFn W0 c) ?_
      exact prf_eq_trans (prf_substtc_consT zero W0 _ _)
        (prf_congr_consT (prf_substtc_tcFn W0 h) (prf_substtc_varc0 W0))
    · refine prf_eq_trans (prf_substtc_consT zero W0 _ _) ?_
      refine prf_congr_consT ?_ ?_
      · exact prf_eq_trans (prf_substtc_liftcT zero W0 _ _)
          (prf_congr_liftcT (prf_substtc_tcFn W0 c) (prf_substtc_tcFn W0 h))
      · exact prf_eq_trans (prf_substtc_liftscT zero W0 _ _)
          (prf_congr_liftscT (prf_substtc_tcFn W0 c) (prf_substtc_varc0 W0))
  have hchain : Prf (substfc zero W0 (substfc (succ zero) W1
      (substfc (succ (succ zero)) W2 (formCode LIFTSC_CONS_BODY)))
      =eq eqCodeFn (liftscT (tcFn c) (consT (tcFn h) (tcFn t)))
            (consT (liftcT (tcFn c) (tcFn h)) (liftscT (tcFn c) (tcFn t)))) :=
    prf_eq_trans (prf_congr_substfc_arg3
      (prf_eq_trans (prf_congr_substfc_arg3 (prf_eq_trans hin hnorm)) hmid)) hout
  exact prf_mp (prf_provCode_congr hchain)
    (pcc_axiom_inst3 LIFTSC_CONS_BODY (show ax_liftsc_cons ∈ axioms by simp [axioms])
      (tcFn c) (tcFn h) (tcFn t))

/-! ## §5 · LA GUARDA INTERNA SE DESCARGA — y las cuatro ecuaciones quedan a NIVEL `zero`

    `pcc_lt_tracked` (`Meta/Delta0ReflectPrf.lean:233`, completitud‑Δ₀ provable del atomo `<`,
    con argumentos **ABIERTOS**) refleja `0 < σn` sin pedir clausura. La guarda de
    `ax_liftc_var_ge` **no es un obstaculo**. -/

theorem pcc_zero_lt_succ_code (n : Term) :
    Prf (provFromCode (ltCodeFn (tcFn zero) (succcT (tcFn n)))) := by
  have h : Prf (provFromCode (ltCodeFn (tcFn zero) (tcFn (succ n)))) :=
    prf_mp (pcc_lt_tracked zero (succ n)) (prf_zero_lt_succ n)
  exact prf_mp (prf_provCode_congr (prf_congr_atom2CodeFn (prf_refl _) (prf_tc_succ' n))) h

theorem pcc_liftc0_var_code (n : Term) :
    Prf (provFromCode (eqCodeFn (liftcT (termCode zero) (varcT (tcFn n)))
      (varcT (succcT (tcFn n))))) := by
  have h := pcc_mp_code_apply (pcc_liftc_var_ge_code zero n) (pcc_zero_lt_succ_code n)
  exact prf_mp (prf_provCode_congr (prf_congr_eqCodeFn
    (prf_congr_liftcT prf_tc_zero (prf_refl _)) (prf_refl _))) h

theorem pcc_liftc0_func_code (a b : Term) :
    Prf (provFromCode (eqCodeFn (liftcT (termCode zero) (funccT (tcFn a) (tcFn b)))
      (funccT (tcFn a) (liftscT (termCode zero) (tcFn b))))) :=
  prf_mp (prf_provCode_congr (prf_congr_eqCodeFn
      (prf_congr_liftcT prf_tc_zero (prf_refl _))
      (prf_congr_funccT (prf_refl _) (prf_congr_liftscT prf_tc_zero (prf_refl _)))))
    (pcc_liftc_func_code zero a b)

theorem pcc_liftsc0_nil_code :
    Prf (provFromCode (eqCodeFn (liftscT (termCode zero) (tcFn nil)) (tcFn nil))) :=
  prf_mp (prf_provCode_congr (prf_congr_eqCodeFn
      (prf_congr_liftscT prf_tc_zero (prf_eq_symm prf_tc_zero)) (prf_eq_symm prf_tc_zero)))
    (pcc_liftsc_nil_code zero)

theorem pcc_liftsc0_cons_code (h t : Term) :
    Prf (provFromCode (eqCodeFn (liftscT (termCode zero) (consT (tcFn h) (tcFn t)))
      (consT (liftcT (termCode zero) (tcFn h)) (liftscT (termCode zero) (tcFn t))))) :=
  prf_mp (prf_provCode_congr (prf_congr_eqCodeFn
      (prf_congr_liftscT prf_tc_zero (prf_refl _))
      (prf_congr_consT (prf_congr_liftcT prf_tc_zero (prf_refl _))
        (prf_congr_liftscT prf_tc_zero (prf_refl _)))))
    (pcc_liftsc_cons_code zero h t)

/-! ## §6 · Congruencias INTERNAS (dentro de `Prov`) para los constructores nuevos.
     Patron `pcc_congr_binT_2_code` (`Meta/CodeCtorKit.lean:248`). -/

theorem pcc_congr_liftcT_arg2_code (A X Y : Term)
    (hA : ∀ W, Prf (substtc zero W A =eq A)) (hX : ∀ W, Prf (substtc zero W X =eq X)) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (liftcT A X) (liftcT A Y))) := by
  let Ac : Term := eqc (liftcT A X) (liftcT A (varc (numeral 0)))
  have hcomp : ∀ w : Term, Prf (substfc zero w Ac =eq eqc (liftcT A X) (liftcT A w)) := by
    intro w
    refine prf_eq_trans (prf_substfc_eq zero w (liftcT A X) (liftcT A (varc (numeral 0)))) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · exact prf_eq_trans (prf_substtc_liftcT zero w A X) (prf_congr_liftcT (hA w) (hX w))
    · exact prf_eq_trans (prf_substtc_liftcT zero w A (varc (numeral 0)))
        (prf_congr_liftcT (hA w) (prf_substtc_varc0 w))
  have hAX : Prf (provFromCode (substfc zero X Ac)) :=
    prf_mp (prf_provCode_congr (prf_eq_symm (hcomp X)))
      (prf_provFromCode_eqCodeFn_refl (liftcT A X))
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcomp Y)) _)
    (PrfH_leibniz_apply Ac X Y (prfH_hyp_self _) (prf_to_prfH hAX _))

theorem pcc_congr_liftscT_arg2_code (A X Y : Term)
    (hA : ∀ W, Prf (substtc zero W A =eq A)) (hX : ∀ W, Prf (substtc zero W X =eq X)) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (liftscT A X) (liftscT A Y))) := by
  let Ac : Term := eqc (liftscT A X) (liftscT A (varc (numeral 0)))
  have hcomp : ∀ w : Term, Prf (substfc zero w Ac =eq eqc (liftscT A X) (liftscT A w)) := by
    intro w
    refine prf_eq_trans (prf_substfc_eq zero w (liftscT A X) (liftscT A (varc (numeral 0)))) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · exact prf_eq_trans (prf_substtc_liftscT zero w A X) (prf_congr_liftscT (hA w) (hX w))
    · exact prf_eq_trans (prf_substtc_liftscT zero w A (varc (numeral 0)))
        (prf_congr_liftscT (hA w) (prf_substtc_varc0 w))
  have hAX : Prf (provFromCode (substfc zero X Ac)) :=
    prf_mp (prf_provCode_congr (prf_eq_symm (hcomp X)))
      (prf_provFromCode_eqCodeFn_refl (liftscT A X))
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcomp Y)) _)
    (PrfH_leibniz_apply Ac X Y (prfH_hyp_self _) (prf_to_prfH hAX _))

/-- Congruencia interna en la COLA de `consT` (para el paso `cons` de la lista). -/
theorem pcc_congr_consT_arg2_code (A X Y : Term)
    (hA : ∀ W, Prf (substtc zero W A =eq A)) (hX : ∀ W, Prf (substtc zero W X =eq X)) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (consT A X) (consT A Y))) := by
  let Ac : Term := eqc (consT A X) (consT A (varc (numeral 0)))
  have hcomp : ∀ w : Term, Prf (substfc zero w Ac =eq eqc (consT A X) (consT A w)) := by
    intro w
    refine prf_eq_trans (prf_substfc_eq zero w (consT A X) (consT A (varc (numeral 0)))) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · exact prf_eq_trans (prf_substtc_consT zero w A X) (prf_congr_consT (hA w) (hX w))
    · exact prf_eq_trans (prf_substtc_consT zero w A (varc (numeral 0)))
        (prf_congr_consT (hA w) (prf_substtc_varc0 w))
  have hAX : Prf (provFromCode (substfc zero X Ac)) :=
    prf_mp (prf_provCode_congr (prf_eq_symm (hcomp X)))
      (prf_provFromCode_eqCodeFn_refl (consT A X))
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcomp Y)) _)
    (PrfH_leibniz_apply Ac X Y (prfH_hyp_self _) (prf_to_prfH hAX _))

/-- Congruencia interna en la CABEZA de `consT`. -/
theorem pcc_congr_consT_arg1_code (B X Y : Term)
    (hB : ∀ W, Prf (substtc zero W B =eq B)) (hX : ∀ W, Prf (substtc zero W X =eq X)) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (consT X B) (consT Y B))) := by
  let Ac : Term := eqc (consT X B) (consT (varc (numeral 0)) B)
  have hcomp : ∀ w : Term, Prf (substfc zero w Ac =eq eqc (consT X B) (consT w B)) := by
    intro w
    refine prf_eq_trans (prf_substfc_eq zero w (consT X B) (consT (varc (numeral 0)) B)) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · exact prf_eq_trans (prf_substtc_consT zero w X B) (prf_congr_consT (hX w) (hB w))
    · exact prf_eq_trans (prf_substtc_consT zero w (varc (numeral 0)) B)
        (prf_congr_consT (prf_substtc_varc0 w) (hB w))
  have hAX : Prf (provFromCode (substfc zero X Ac)) :=
    prf_mp (prf_provCode_congr (prf_eq_symm (hcomp X)))
      (prf_provFromCode_eqCodeFn_refl (consT X B))
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcomp Y)) _)
    (PrfH_leibniz_apply Ac X Y (prfH_hyp_self _) (prf_to_prfH hAX _))
theorem iz_inv : ∀ W, Prf (substtc zero W (termCode zero) =eq termCode zero) :=
  fun W => prf_substtc_termCode_zero 0 W

/-- **(1) BASE `varc` — CERRADA, sin hipotesis mas alla de la forma ecuacional.** -/
theorem refl_caso_varc (s a : Term) (hs : Prf (s =eq varc a)) : Prf (targetLift s) := by
  unfold targetLift
  have hplain : Prf (liftc zero s =eq varc (succ a)) :=
    prf_eq_trans (prf_congr_liftc hs) (prf_mp (prf_liftc_var_ge zero a) (prf_zero_lt_succ a))
  have hX : ∀ W, Prf (substtc zero W (liftcT (termCode zero) (tcFn (varc a)))
      =eq liftcT (termCode zero) (tcFn (varc a))) :=
    substtc_inv_liftcT iz_inv (substtc_inv_tcFn (varc a))
  have hY : ∀ W, Prf (substtc zero W (liftcT (termCode zero) (varcT (tcFn a)))
      =eq liftcT (termCode zero) (varcT (tcFn a))) :=
    substtc_inv_liftcT iz_inv (substtc_inv_unT (substtc_inv_tcFn a))
  have s1 : Prf (provFromCode (eqc (liftcT (termCode zero) (tcFn (varc a)))
      (liftcT (termCode zero) (varcT (tcFn a))))) :=
    prf_mp (pcc_congr_liftcT_arg2_code (termCode zero) (tcFn (varc a)) (varcT (tcFn a))
      iz_inv (substtc_inv_tcFn (varc a))) (pcc_dot_un_symm 0 a)
  have s2 : Prf (provFromCode (eqc (liftcT (termCode zero) (varcT (tcFn a)))
      (varcT (succcT (tcFn a))))) := pcc_liftc0_var_code a
  have s3 : Prf (provFromCode (eqc (varcT (succcT (tcFn a))) (tcFn (varc (succ a))))) :=
    prf_mp (prf_provCode_congr (prf_congr_eqCodeFn
      (prf_congr_varcT (prf_tc_succ' a)) (prf_refl _)))
      (pcc_dot_un 0 (succ a))
  have hchain : Prf (provFromCode (eqc (liftcT (termCode zero) (tcFn (varc a)))
      (tcFn (varc (succ a))))) :=
    pcc_eq_trans_code _ _ _ hX s1 (pcc_eq_trans_code _ _ _ hY s2 s3)
  exact prf_mp (prf_provCode_congr (prf_congr_eqCodeFn
    (prf_congr_liftcT (prf_refl _) (prf_congr_tcFn (prf_eq_symm hs)))
    (prf_congr_tcFn (prf_eq_symm hplain)))) hchain

/-- **(2) PASO `funcc`** — el unico salto: pide la companera sobre la LISTA de argumentos. -/
theorem refl_caso_funcc (s p b : Term) (hs : Prf (s =eq funcc p b))
    (hb : Prf (targetLiftsc b)) : Prf (targetLift s) := by
  unfold targetLift
  unfold targetLiftsc at hb
  have hplain : Prf (liftc zero s =eq funcc p (liftsc zero b)) :=
    prf_eq_trans (prf_congr_liftc hs) (prf_liftc_func zero p b)
  have hX : ∀ W, Prf (substtc zero W (liftcT (termCode zero) (tcFn (funcc p b)))
      =eq liftcT (termCode zero) (tcFn (funcc p b))) :=
    substtc_inv_liftcT iz_inv (substtc_inv_tcFn (funcc p b))
  have hY : ∀ W, Prf (substtc zero W (liftcT (termCode zero) (funccT (tcFn p) (tcFn b)))
      =eq liftcT (termCode zero) (funccT (tcFn p) (tcFn b))) :=
    substtc_inv_liftcT iz_inv
      (substtc_inv_binT (substtc_inv_tcFn p) (substtc_inv_tcFn b))
  have hZ : ∀ W, Prf (substtc zero W
      (funccT (tcFn p) (liftscT (termCode zero) (tcFn b)))
      =eq funccT (tcFn p) (liftscT (termCode zero) (tcFn b))) :=
    substtc_inv_binT (substtc_inv_tcFn p)
      (substtc_inv_liftscT iz_inv (substtc_inv_tcFn b))
  have s1 : Prf (provFromCode (eqc (liftcT (termCode zero) (tcFn (funcc p b)))
      (liftcT (termCode zero) (funccT (tcFn p) (tcFn b))))) :=
    prf_mp (pcc_congr_liftcT_arg2_code (termCode zero) (tcFn (funcc p b))
      (funccT (tcFn p) (tcFn b)) iz_inv (substtc_inv_tcFn (funcc p b)))
      (pcc_dot_bin_symm 1 p b)
  have s2 : Prf (provFromCode (eqc (liftcT (termCode zero) (funccT (tcFn p) (tcFn b)))
      (funccT (tcFn p) (liftscT (termCode zero) (tcFn b))))) := pcc_liftc0_func_code p b
  have s3 : Prf (provFromCode (eqc (funccT (tcFn p) (liftscT (termCode zero) (tcFn b)))
      (funccT (tcFn p) (tcFn (liftsc zero b))))) :=
    prf_mp (pcc_congr_binT_2_code 1 (tcFn p) (liftscT (termCode zero) (tcFn b))
      (tcFn (liftsc zero b)) (substtc_inv_tcFn p)
      (substtc_inv_liftscT iz_inv (substtc_inv_tcFn b))) hb
  have s4 : Prf (provFromCode (eqc (funccT (tcFn p) (tcFn (liftsc zero b)))
      (tcFn (funcc p (liftsc zero b))))) := pcc_dot_bin 1 p (liftsc zero b)
  have hchain : Prf (provFromCode (eqc (liftcT (termCode zero) (tcFn (funcc p b)))
      (tcFn (funcc p (liftsc zero b))))) :=
    pcc_eq_trans_code _ _ _ hX s1
      (pcc_eq_trans_code _ _ _ hY s2 (pcc_eq_trans_code _ _ _ hZ s3 s4))
  exact prf_mp (prf_provCode_congr (prf_congr_eqCodeFn
    (prf_congr_liftcT (prf_refl _) (prf_congr_tcFn (prf_eq_symm hs)))
    (prf_congr_tcFn (prf_eq_symm hplain)))) hchain

/-- **(3) BASE de la LISTA (`nil`) — CERRADA, sin hipotesis ninguna.** -/
theorem refl_lista_nil : Prf (targetLiftsc nil) := by
  unfold targetLiftsc
  exact prf_mp (prf_provCode_congr (prf_congr_eqCodeFn (prf_refl _)
    (prf_congr_tcFn (prf_eq_symm (prf_liftsc_nil zero))))) pcc_liftsc0_nil_code

/-- **(4) PASO de la LISTA (`cons`)** — pide la companera sobre la cabeza y sobre la cola. -/
theorem refl_lista_cons (h t : Term) (hh : Prf (targetLift h)) (ht : Prf (targetLiftsc t)) :
    Prf (targetLiftsc (cons h t)) := by
  unfold targetLift at hh
  unfold targetLiftsc at ht ⊢
  have hplain : Prf (liftsc zero (cons h t) =eq cons (liftc zero h) (liftsc zero t)) :=
    prf_liftsc_cons zero h t
  have hX : ∀ W, Prf (substtc zero W (liftscT (termCode zero) (tcFn (cons h t)))
      =eq liftscT (termCode zero) (tcFn (cons h t))) :=
    substtc_inv_liftscT iz_inv (substtc_inv_tcFn (cons h t))
  have hY : ∀ W, Prf (substtc zero W (liftscT (termCode zero) (consT (tcFn h) (tcFn t)))
      =eq liftscT (termCode zero) (consT (tcFn h) (tcFn t))) :=
    substtc_inv_liftscT iz_inv (substtc_inv_consT (substtc_inv_tcFn h) (substtc_inv_tcFn t))
  have hZ : ∀ W, Prf (substtc zero W
      (consT (liftcT (termCode zero) (tcFn h)) (liftscT (termCode zero) (tcFn t)))
      =eq consT (liftcT (termCode zero) (tcFn h)) (liftscT (termCode zero) (tcFn t))) :=
    substtc_inv_consT (substtc_inv_liftcT iz_inv (substtc_inv_tcFn h))
      (substtc_inv_liftscT iz_inv (substtc_inv_tcFn t))
  have hU : ∀ W, Prf (substtc zero W
      (consT (tcFn (liftc zero h)) (liftscT (termCode zero) (tcFn t)))
      =eq consT (tcFn (liftc zero h)) (liftscT (termCode zero) (tcFn t))) :=
    substtc_inv_consT (substtc_inv_tcFn (liftc zero h))
      (substtc_inv_liftscT iz_inv (substtc_inv_tcFn t))
  have s1 : Prf (provFromCode (eqc (liftscT (termCode zero) (tcFn (cons h t)))
      (liftscT (termCode zero) (consT (tcFn h) (tcFn t))))) :=
    prf_mp (pcc_congr_liftscT_arg2_code (termCode zero) (tcFn (cons h t))
      (consT (tcFn h) (tcFn t)) iz_inv (substtc_inv_tcFn (cons h t)))
      (pcc_dot_cons_symm h t)
  have s2 : Prf (provFromCode (eqc (liftscT (termCode zero) (consT (tcFn h) (tcFn t)))
      (consT (liftcT (termCode zero) (tcFn h)) (liftscT (termCode zero) (tcFn t))))) :=
    pcc_liftsc0_cons_code h t
  have s3 : Prf (provFromCode (eqc
      (consT (liftcT (termCode zero) (tcFn h)) (liftscT (termCode zero) (tcFn t)))
      (consT (tcFn (liftc zero h)) (liftscT (termCode zero) (tcFn t))))) :=
    prf_mp (pcc_congr_consT_arg1_code (liftscT (termCode zero) (tcFn t))
      (liftcT (termCode zero) (tcFn h)) (tcFn (liftc zero h))
      (substtc_inv_liftscT iz_inv (substtc_inv_tcFn t))
      (substtc_inv_liftcT iz_inv (substtc_inv_tcFn h))) hh
  have s4 : Prf (provFromCode (eqc
      (consT (tcFn (liftc zero h)) (liftscT (termCode zero) (tcFn t)))
      (consT (tcFn (liftc zero h)) (tcFn (liftsc zero t))))) :=
    prf_mp (pcc_congr_consT_arg2_code (tcFn (liftc zero h))
      (liftscT (termCode zero) (tcFn t)) (tcFn (liftsc zero t))
      (substtc_inv_tcFn (liftc zero h))
      (substtc_inv_liftscT iz_inv (substtc_inv_tcFn t))) ht
  have s5 : Prf (provFromCode (eqc
      (consT (tcFn (liftc zero h)) (tcFn (liftsc zero t)))
      (tcFn (cons (liftc zero h) (liftsc zero t))))) :=
    pcc_dot_cons (liftc zero h) (liftsc zero t)
  have hchain : Prf (provFromCode (eqc (liftscT (termCode zero) (tcFn (cons h t)))
      (tcFn (cons (liftc zero h) (liftsc zero t))))) :=
    pcc_eq_trans_code _ _ _ hX s1
      (pcc_eq_trans_code _ _ _ hY s2
        (pcc_eq_trans_code _ _ _ hZ s3
          (pcc_eq_trans_code _ _ _ hU s4 s5)))
  exact prf_mp (prf_provCode_congr (prf_congr_eqCodeFn (prf_refl _)
    (prf_congr_tcFn (prf_eq_symm hplain)))) hchain
theorem substF_targetLift_hole (t : Term) :
    substFormula 0 t (provFromCode (eqc (liftcT (termCode zero) (tcFn (.var 0)))
        (tcFn (liftc zero (.var 0)))))
      = targetLift t := by
  simp only [targetLift, substFormula_provFromCode_open, eqc, liftcT, funcc, tcFn, liftc,
    cons, nil, zero, succ, substTerm, substTerms, substTerm_termCode, substTerm_strCode, if_true]

theorem PrfH_congr_targetLift {Γ : List Formula} {s s' : Term} (h : PrfH Γ (s =eq s'))
    (ha : PrfH Γ (targetLift s)) : PrfH Γ (targetLift s') :=
  (substF_targetLift_hole s') ▸
    PrfH_leibniz_subst
      (A := provFromCode (eqc (liftcT (termCode zero) (tcFn (.var 0)))
        (tcFn (liftc zero (.var 0))))) h ((substF_targetLift_hole s) ▸ ha)

/-- **EL DISYUNTO `varc`, EN LA MONEDA QUE PIDE LA INDUCCION OBJETO** (implicacion interna,
    guarda como HIPOTESIS): `⊢ shapeUn X 0 ⇒ targetLift X`. CERRADO, sin hipotesis. -/
theorem refl_shapeUn_imp (X : Term) : Prf (Formula.impl (shapeUn X 0) (targetLift X)) := by
  refine prf_deduction ?_
  let a : Term := nthc X (numeralM 1)
  have hh : PrfH [shapeUn X 0] (Formula.eq X (varc a)) := prfH_hyp_self _
  exact PrfH_congr_targetLift (PrfH_eq_symm hh)
    (prf_to_prfH (refl_caso_varc (varc a) a (prf_refl _)) _)
/-! ### El disyunto `funcc`: la HI llega tambien como hipotesis OBJETO -/

/-- Transitividad interna de `=` **en contexto `PrfH`** (para mezclar hechos libres con la HI). -/
theorem PrfH_eq_trans_code {Γ : List Formula} (X Y Z : Term)
    (hX : ∀ W, Prf (substtc zero W X =eq X))
    (h1 : PrfH Γ (provFromCode (eqc X Y))) (h2 : PrfH Γ (provFromCode (eqc Y Z))) :
    PrfH Γ (provFromCode (eqc X Z)) := by
  let Ac : Term := eqc X (varc (numeral 0))
  have hcomp : ∀ t : Term, Prf (substfc zero t Ac =eq eqc X t) := fun t =>
    prf_eq_trans (prf_substfc_eq zero t X (varc (numeral 0)))
      (prf_congr_eqCodeFn (hX t) (prf_substtc_varc0 t))
  have hY : PrfH Γ (provFromCode (substfc zero Y Ac)) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_eq_symm (hcomp Y))) _) h1
  have hZ : PrfH Γ (provFromCode (substfc zero Z Ac)) := PrfH_leibniz_apply Ac Y Z h2 hY
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcomp Z)) _) hZ

/-- **(2') PASO `funcc`, en forma IMPLICACION**: la companera de la lista entra como
    hipotesis OBJETO. Es la moneda que consume una induccion objeto. -/
theorem refl_caso_funcc_imp (p b : Term) :
    Prf (Formula.impl (targetLiftsc b) (targetLift (funcc p b))) := by
  refine prf_deduction ?_
  have hb : PrfH [targetLiftsc b] (targetLiftsc b) := prfH_hyp_self _
  have hX : ∀ W, Prf (substtc zero W (liftcT (termCode zero) (tcFn (funcc p b)))
      =eq liftcT (termCode zero) (tcFn (funcc p b))) :=
    substtc_inv_liftcT iz_inv (substtc_inv_tcFn (funcc p b))
  have hY : ∀ W, Prf (substtc zero W (liftcT (termCode zero) (funccT (tcFn p) (tcFn b)))
      =eq liftcT (termCode zero) (funccT (tcFn p) (tcFn b))) :=
    substtc_inv_liftcT iz_inv (substtc_inv_binT (substtc_inv_tcFn p) (substtc_inv_tcFn b))
  have hZ : ∀ W, Prf (substtc zero W (funccT (tcFn p) (liftscT (termCode zero) (tcFn b)))
      =eq funccT (tcFn p) (liftscT (termCode zero) (tcFn b))) :=
    substtc_inv_binT (substtc_inv_tcFn p) (substtc_inv_liftscT iz_inv (substtc_inv_tcFn b))
  have s1 : PrfH [targetLiftsc b] (provFromCode (eqc
      (liftcT (termCode zero) (tcFn (funcc p b)))
      (liftcT (termCode zero) (funccT (tcFn p) (tcFn b))))) :=
    prf_to_prfH (prf_mp (pcc_congr_liftcT_arg2_code (termCode zero) (tcFn (funcc p b))
      (funccT (tcFn p) (tcFn b)) iz_inv (substtc_inv_tcFn (funcc p b)))
      (pcc_dot_bin_symm 1 p b)) _
  have s2 : PrfH [targetLiftsc b] (provFromCode (eqc
      (liftcT (termCode zero) (funccT (tcFn p) (tcFn b)))
      (funccT (tcFn p) (liftscT (termCode zero) (tcFn b))))) :=
    prf_to_prfH (pcc_liftc0_func_code p b) _
  have s3 : PrfH [targetLiftsc b] (provFromCode (eqc
      (funccT (tcFn p) (liftscT (termCode zero) (tcFn b)))
      (funccT (tcFn p) (tcFn (liftsc zero b))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_congr_binT_2_code 1 (tcFn p)
      (liftscT (termCode zero) (tcFn b)) (tcFn (liftsc zero b)) (substtc_inv_tcFn p)
      (substtc_inv_liftscT iz_inv (substtc_inv_tcFn b))) _) hb
  have s4 : PrfH [targetLiftsc b] (provFromCode (eqc
      (funccT (tcFn p) (tcFn (liftsc zero b))) (tcFn (funcc p (liftsc zero b))))) :=
    prf_to_prfH (pcc_dot_bin 1 p (liftsc zero b)) _
  have hchain : PrfH [targetLiftsc b] (provFromCode (eqc
      (liftcT (termCode zero) (tcFn (funcc p b))) (tcFn (funcc p (liftsc zero b))))) :=
    PrfH_eq_trans_code _ _ _ hX s1
      (PrfH_eq_trans_code _ _ _ hY s2 (PrfH_eq_trans_code _ _ _ hZ s3 s4))
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_congr_eqCodeFn (prf_refl _)
    (prf_congr_tcFn (prf_eq_symm (prf_liftc_func zero p b))))) _) hchain

/-- **EL DISYUNTO `funcc`, EN LA MONEDA DE LA INDUCCION OBJETO**:
    `⊢ (shapeBin X 1 ∧ targetLiftsc (nthc X 2̄)) ⇒ targetLift X`. -/
theorem refl_shapeBin_imp (X : Term) :
    Prf (Formula.impl (land (shapeBin X 1) (targetLiftsc (nthc X (numeralM 2))))
      (targetLift X)) := by
  refine prf_deduction ?_
  let p : Term := nthc X (numeralM 1)
  let b : Term := nthc X (numeralM 2)
  let H : Formula := land (shapeBin X 1) (targetLiftsc b)
  have hh : PrfH [H] H := prfH_hyp_self _
  have hs : PrfH [H] (Formula.eq X (funcc p b)) := PrfH_and_elim_left hh
  have hb : PrfH [H] (targetLiftsc b) := PrfH_and_elim_right hh
  have hfb : PrfH [H] (targetLift (funcc p b)) :=
    PrfH.mp _ _ _ (prf_to_prfH (refl_caso_funcc_imp p b) _) hb
  exact PrfH_congr_targetLift (PrfH_eq_symm hs) hfb

/-- **(4') PASO de la LISTA, en forma IMPLICACION.** -/
theorem refl_lista_cons_imp (h t : Term) :
    Prf (Formula.impl (land (targetLift h) (targetLiftsc t)) (targetLiftsc (cons h t))) := by
  refine prf_deduction ?_
  let H : Formula := land (targetLift h) (targetLiftsc t)
  have hh0 : PrfH [H] H := prfH_hyp_self _
  have hh : PrfH [H] (targetLift h) := PrfH_and_elim_left hh0
  have ht : PrfH [H] (targetLiftsc t) := PrfH_and_elim_right hh0
  have hX : ∀ W, Prf (substtc zero W (liftscT (termCode zero) (tcFn (cons h t)))
      =eq liftscT (termCode zero) (tcFn (cons h t))) :=
    substtc_inv_liftscT iz_inv (substtc_inv_tcFn (cons h t))
  have hY : ∀ W, Prf (substtc zero W (liftscT (termCode zero) (consT (tcFn h) (tcFn t)))
      =eq liftscT (termCode zero) (consT (tcFn h) (tcFn t))) :=
    substtc_inv_liftscT iz_inv (substtc_inv_consT (substtc_inv_tcFn h) (substtc_inv_tcFn t))
  have hZ : ∀ W, Prf (substtc zero W
      (consT (liftcT (termCode zero) (tcFn h)) (liftscT (termCode zero) (tcFn t)))
      =eq consT (liftcT (termCode zero) (tcFn h)) (liftscT (termCode zero) (tcFn t))) :=
    substtc_inv_consT (substtc_inv_liftcT iz_inv (substtc_inv_tcFn h))
      (substtc_inv_liftscT iz_inv (substtc_inv_tcFn t))
  have hU : ∀ W, Prf (substtc zero W
      (consT (tcFn (liftc zero h)) (liftscT (termCode zero) (tcFn t)))
      =eq consT (tcFn (liftc zero h)) (liftscT (termCode zero) (tcFn t))) :=
    substtc_inv_consT (substtc_inv_tcFn (liftc zero h))
      (substtc_inv_liftscT iz_inv (substtc_inv_tcFn t))
  have s1 : PrfH [H] (provFromCode (eqc (liftscT (termCode zero) (tcFn (cons h t)))
      (liftscT (termCode zero) (consT (tcFn h) (tcFn t))))) :=
    prf_to_prfH (prf_mp (pcc_congr_liftscT_arg2_code (termCode zero) (tcFn (cons h t))
      (consT (tcFn h) (tcFn t)) iz_inv (substtc_inv_tcFn (cons h t)))
      (pcc_dot_cons_symm h t)) _
  have s2 : PrfH [H] (provFromCode (eqc (liftscT (termCode zero) (consT (tcFn h) (tcFn t)))
      (consT (liftcT (termCode zero) (tcFn h)) (liftscT (termCode zero) (tcFn t))))) :=
    prf_to_prfH (pcc_liftsc0_cons_code h t) _
  have s3 : PrfH [H] (provFromCode (eqc
      (consT (liftcT (termCode zero) (tcFn h)) (liftscT (termCode zero) (tcFn t)))
      (consT (tcFn (liftc zero h)) (liftscT (termCode zero) (tcFn t))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_congr_consT_arg1_code (liftscT (termCode zero) (tcFn t))
      (liftcT (termCode zero) (tcFn h)) (tcFn (liftc zero h))
      (substtc_inv_liftscT iz_inv (substtc_inv_tcFn t))
      (substtc_inv_liftcT iz_inv (substtc_inv_tcFn h))) _) hh
  have s4 : PrfH [H] (provFromCode (eqc
      (consT (tcFn (liftc zero h)) (liftscT (termCode zero) (tcFn t)))
      (consT (tcFn (liftc zero h)) (tcFn (liftsc zero t))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_congr_consT_arg2_code (tcFn (liftc zero h))
      (liftscT (termCode zero) (tcFn t)) (tcFn (liftsc zero t))
      (substtc_inv_tcFn (liftc zero h))
      (substtc_inv_liftscT iz_inv (substtc_inv_tcFn t))) _) ht
  have s5 : PrfH [H] (provFromCode (eqc
      (consT (tcFn (liftc zero h)) (tcFn (liftsc zero t)))
      (tcFn (cons (liftc zero h) (liftsc zero t))))) :=
    prf_to_prfH (pcc_dot_cons (liftc zero h) (liftsc zero t)) _
  have hchain : PrfH [H] (provFromCode (eqc (liftscT (termCode zero) (tcFn (cons h t)))
      (tcFn (cons (liftc zero h) (liftsc zero t))))) :=
    PrfH_eq_trans_code _ _ _ hX s1
      (PrfH_eq_trans_code _ _ _ hY s2
        (PrfH_eq_trans_code _ _ _ hZ s3 (PrfH_eq_trans_code _ _ _ hU s4 s5)))
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_congr_eqCodeFn (prf_refl _)
    (prf_congr_tcFn (prf_eq_symm (prf_liftsc_cons zero h t))))) _) hchain
theorem impT {A B C : Formula} (h1 : Prf (A ⇒ B)) (h2 : Prf (B ⇒ C)) : Prf (A ⇒ C) := by
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH h2 _) (PrfH.mp _ _ _ (prf_to_prfH h1 _) (prfH_hyp_self _))

theorem prf_or_elim_imp {A B C : Formula} (h1 : Prf (A ⇒ C)) (h2 : Prf (B ⇒ C)) :
    Prf (lor A B ⇒ C) := by
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (PrfH.mp _ _ _
    (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prfᵢ.j3 A B C)) (prfH_hyp_self _))
    (prf_to_prfH h1 _)) (prf_to_prfH h2 _)

/-! ## §7 - COPIA LITERAL de sondeos/ClausuraLiftSinWTs.lean (piezas sueltas + §5 entero) -/

theorem prf_cdrc_cons (h t : Term) : Prf (cdrc (cons h t) =eq t) := by
  have hax : Prf ax_cdrc := prf_ax (by simp [axioms])
  have hh := prf_spec (prf_spec hax h) t
  simp [substFormula, substTerm, substTerms, cdrc, cons, FOL.substTerm_liftTerm] at hh
  exact hh
def consOk (X : Term) : Formula := Formula.eq X (cons (carc X) (cdrc X))
theorem prf_consOk_cons (a b : Term) : Prf (consOk (cons a b)) :=
  prf_eq_trans (prf_congr_cons_head (prf_eq_symm (prf_carc_cons a b)))
    (prf_congr_cons_tail (prf_eq_symm (prf_cdrc_cons a b)))
theorem PrfH_congr_lenc {Γ : List Formula} {a b : Term} (h : PrfH Γ (a =eq b)) :
    PrfH Γ (lenc a =eq lenc b) := by
  let f : Formula := Formula.eq (lenc (liftTerm 0 a)) (lenc (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (lenc a) (lenc s) := by
    intro s
    simp only [f, lenc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS b) ▸ PrfH_leibniz_subst (A := f) h ((hS a) ▸ prf_to_prfH (prf_refl (lenc a)) Γ)
theorem PrfH_congr_nthc_lst {Γ : List Formula} {a b : Term} (i : Term) (h : PrfH Γ (a =eq b)) :
    PrfH Γ (nthc a i =eq nthc b i) := by
  let f : Formula := Formula.eq (nthc (liftTerm 0 a) (liftTerm 0 i)) (nthc (.var 0) (liftTerm 0 i))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (nthc a i) (nthc s i) := by
    intro s
    simp only [f, nthc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS b) ▸ PrfH_leibniz_subst (A := f) h ((hS a) ▸ prf_to_prfH (prf_refl (nthc a i)) Γ)
theorem PrfH_congr_In_left {Γ : List Formula} {u v w : Term} (h : PrfH Γ (u =eq v))
    (hin : PrfH Γ (In u w)) : PrfH Γ (In v w) := by
  have hS : ∀ s : Term, substFormula 0 s (In (.var 0) (liftTerm 0 w)) = In s w := by
    intro s
    simp only [In, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS v) ▸ PrfH_leibniz_subst (A := In (.var 0) (liftTerm 0 w)) h ((hS u) ▸ hin)
theorem PrfH_congr_argsIn {Γ : List Formula} {wT Y₁ Y₂ : Term} (h : PrfH Γ (Y₁ =eq Y₂))
    (ha : PrfH Γ (argsIn wT Y₁)) : PrfH Γ (argsIn wT Y₂) := by
  have hS : ∀ s : Term, substFormula 0 s (argsIn (liftTerm 0 wT) (.var 0)) = argsIn wT s := by
    intro s
    simp only [substF_argsIn, substTerm, FOL.substTerm_liftTerm, if_true]
  exact (hS Y₂) ▸ PrfH_leibniz_subst (A := argsIn (liftTerm 0 wT) (.var 0)) h ((hS Y₁) ▸ ha)
theorem PrfH_congr_isTermCodeE1 {Γ : List Formula} {wT X₁ X₂ : Term} (h : PrfH Γ (X₁ =eq X₂))
    (ha : PrfH Γ (isTermCodeE1 wT X₁)) : PrfH Γ (isTermCodeE1 wT X₂) := by
  have hS : ∀ s : Term,
      substFormula 0 s (isTermCodeE1 (liftTerm 0 wT) (.var 0)) = isTermCodeE1 wT s := by
    intro s
    simp only [substF_isTermCodeE1, substTerm, FOL.substTerm_liftTerm, if_true]
  exact (hS X₂) ▸ PrfH_leibniz_subst (A := isTermCodeE1 (liftTerm 0 wT) (.var 0)) h ((hS X₁) ▸ ha)
theorem PrfH_inst_argsIn {Γ : List Formula} (wT Y i : Term) (h : PrfH Γ (argsIn wT Y)) :
    PrfH Γ (Formula.impl (lt i (lenc Y)) (In (nthc Y i) wT)) := by
  have hi := PrfH_spec h i
  simpa only [argsInBody, lt, lenc, nthc, In, substFormula, substTerm, substTerms,
    FOL.substTerm_liftTerm, if_true] using hi
theorem PrfH_inst_wfAll1 {Γ : List Formula} (w i : Term) (h : PrfH Γ (wfAll1 w)) :
    PrfH Γ (Formula.impl (lt i (lenc w)) (isTermCodeE1 w (nthc w i))) := by
  have hi := PrfH_spec h i
  simpa only [wfAll1Body, isTermCodeE1, shapeUn, shapeBin, argsIn, argsInBody, lor, land,
    lt, lenc, nthc, In, cons, nil, zero, substFormula, substTerm, substTerms,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceGT, Nat.reduceSub, Nat.reduceEqDiff, reduceIte,
    FOL.substTerm_liftTerm, FOL.substTerm_lift_comm_zero, substTerm_numeralM, if_true] using hi
theorem prf_nthc_c1 (a b c : Term) : Prf (nthc (cons a (cons b c)) (numeralM 1) =eq b) :=
  prf_eq_trans (prf_nthc_succ a (cons b c) (numeralM 0)) (prf_nthc_zero b c)

theorem prf_nthc_c2 (a b c d : Term) :
    Prf (nthc (cons a (cons b (cons c d))) (numeralM 2) =eq c) :=
  prf_eq_trans (prf_nthc_succ a (cons b (cons c d)) (numeralM 1)) (prf_nthc_c1 b c d)
/-! ## 5 · NO VACUIDAD — todo termino REAL tiene testigo, y el testigo es UNA SOLA LISTA

    ⚠️ Sin esto la via no vale nada: el predicado podria ser vacio. Aqui se comprueba que
    `tcodes1 t` (los codigos de TERMINO de los subterminos de `t`, **sin** la lista de
    codigos de LISTA que `sondeos/DiscriminaEcuacional.lean` necesitaba) YA es testigo. -/

theorem prf_congr_argsIn {wT Y₁ Y₂ : Term} (h : Prf (Y₁ =eq Y₂)) (ha : Prf (argsIn wT Y₁)) :
    Prf (argsIn wT Y₂) :=
  prfH_nil_to_prf (PrfH_congr_argsIn (prf_to_prfH h []) (prf_to_prfH ha [])) rfl

theorem prf_congr_In_left {u v w : Term} (h : Prf (u =eq v)) (hin : Prf (In u w)) :
    Prf (In v w) :=
  prfH_nil_to_prf (PrfH_congr_In_left (prf_to_prfH h []) (prf_to_prfH hin [])) rfl

theorem prf_orL {A B : Formula} (h : Prf A) : Prf (lor A B) :=
  prf_mp (Prf.incl (Prfᵢ.j1 A B)) h
theorem prf_orR {A B : Formula} (h : Prf B) : Prf (lor A B) :=
  prf_mp (Prf.incl (Prfᵢ.j2 A B)) h

/-! ### `∀` acotado con cota ABSTRACTA igual a un numeral (copia del piloto §3) -/

theorem prf_bdAll_numeral (Φ : Formula) (hΦ : substFormula 0 (.var 0) Φ = Φ) : ∀ (n : Nat),
    (∀ k : Nat, k < n → Prf (substFormula 0 (numeralM k) Φ)) →
      Prf (Formula.forall (Formula.impl (lt (.var 0) (numeralM n)) Φ))
  | 0, _ => by
      refine Prf.gen _ (prf_deduction ?_)
      exact PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prfᵢ.efq Φ))
        (PrfH.mp _ _ _ (prf_to_prfH (prf_not_lt_zero (.var 0)) _)
          (PrfH.hyp _ _ (List.Mem.head _)))
  | n + 1, h => by
      have ih := prf_bdAll_numeral Φ hΦ n (fun k hk => h k (Nat.lt_succ_of_lt hk))
      have hself : substFormula 0 (.var 0) (Formula.impl (lt (.var 0) (numeralM n)) Φ)
          = Formula.impl (lt (.var 0) (numeralM n)) Φ := by
        simp only [substFormula, lt, substTerm, substTerms, substTerm_numeralM, hΦ, if_true]
      refine Prf.gen _ (prf_deduction ?_)
      have hsplit : PrfH [lt (.var 0) (numeralM (n + 1))]
          (lor (lt (.var 0) (numeralM n)) (Formula.eq (.var 0) (numeralM n))) :=
        PrfH.mp _ _ _ (prf_to_prfH (prf_lt_succ_split (.var 0) (numeralM n)) _)
          (PrfH.hyp _ _ (List.Mem.head _))
      refine PrfH_or_elim hsplit ?brA ?brB
      case brA =>
        exact PrfH.mp _ _ _ (prf_to_prfH (hself ▸ prf_spec ih (.var 0)) _)
          (PrfH.hyp _ _ (List.Mem.head _))
      case brB =>
        have hinst : Prf (substFormula 0 (numeralM n) Φ) := h n (Nat.lt_succ_self n)
        have heq : PrfH (Formula.eq (.var 0) (numeralM n) :: [lt (.var 0) (numeralM (n + 1))])
            (Formula.eq (numeralM n) (.var 0)) :=
          PrfH_eq_symm (PrfH.hyp _ _ (List.Mem.head _))
        have := PrfH_leibniz_subst (A := Φ) heq (prf_to_prfH hinst _)
        rwa [hΦ] at this

theorem prf_bdAll_of_bound (Φ : Formula) (b : Term) (n : Nat)
    (hΦ : substFormula 0 (.var 0) Φ = Φ)
    (hb : Prf (Formula.eq b (numeralM n)))
    (h : ∀ k : Nat, k < n → Prf (substFormula 0 (numeralM k) Φ)) :
    Prf (Formula.forall (Formula.impl (lt (.var 0) b) Φ)) := by
  have key : Prf (Formula.forall (Formula.impl (lt (.var 0) (numeralM n)) Φ)) :=
    prf_bdAll_numeral Φ hΦ n h
  have hself : substFormula 0 (.var 0) (Formula.impl (lt (.var 0) (numeralM n)) Φ)
      = Formula.impl (lt (.var 0) (numeralM n)) Φ := by
    simp only [substFormula, lt, substTerm, substTerms, substTerm_numeralM, hΦ, if_true]
  refine Prf.gen _ (prf_deduction ?_)
  exact PrfH.mp _ _ _ (prf_to_prfH (hself ▸ prf_spec key (.var 0)) _)
    (ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2
      (prf_to_prfH hb _) (PrfH.hyp _ _ (List.Mem.head _)))

/-! ### Los dos moldes de nodo, ya en forma ECUACIONAL -/

theorem prf_isTermCodeE1_var (W a : Term) : Prf (isTermCodeE1 W (varc a)) :=
  prf_orL (prf_eq_symm (prf_congr_cons_tail (prf_congr_cons_head
    (prf_nthc_c1 (numeralM 0) a nil))))

theorem prf_isTermCodeE1_func (W S C : Term) (h : Prf (argsIn W C)) :
    Prf (isTermCodeE1 W (funcc S C)) :=
  prf_orR (prf_and_intro
    (prf_eq_symm (prf_congr_cons_tail (prf_eq_trans
      (prf_congr_cons_head (prf_nthc_c1 (numeralM 1) S (cons C nil)))
      (prf_congr_cons_tail (prf_congr_cons_head (prf_nthc_c2 (numeralM 1) S C nil))))))
    (prf_congr_argsIn (prf_eq_symm (prf_nthc_c2 (numeralM 1) S C nil)) h))

/-- Introduccion de `argsIn` para una lista CONCRETA (cota numeral). -/
theorem prf_argsIn_of_closed (W C : Term) (n : Nat)
    (hWl : liftTerm 0 W = W) (hCl : liftTerm 0 C = C)
    (hWs : ∀ (v : Nat) (s : Term), substTerm v s W = W)
    (hCs : ∀ (v : Nat) (s : Term), substTerm v s C = C)
    (hlen : Prf (lenc C =eq numeralM n))
    (h : ∀ k : Nat, k < n → Prf (In (nthc C (numeralM k)) W)) :
    Prf (argsIn W C) := by
  have hAI : argsIn W C
      = Formula.forall (Formula.impl (lt (.var 0) (lenc C)) (In (nthc C (.var 0)) W)) := by
    simp only [argsIn, argsInBody, lt, lenc, nthc, In, liftTerm, liftTerms, hWl, hCl]
  rw [hAI]
  refine prf_bdAll_of_bound _ (lenc C) n ?_ hlen ?_
  · simp only [In, nthc, substFormula, substTerm, substTerms, hWs, hCs, if_true]
  · intro k hk
    have hk' := h k hk
    simpa only [In, nthc, substFormula, substTerm, substTerms, hWs, hCs,
      substTerm_numeralM, if_true, reduceIte] using hk'

/-! ### `lenc`/`nthc` de `termsCodeM` (la lista de argumentos REAL) -/

theorem prf_lenc_termsCodeM : ∀ ts : List Term,
    Prf (lenc (termsCodeM ts) =eq numeralM ts.length)
  | []      => prf_lenc_nil
  | t :: ts =>
      prf_eq_trans (prf_lenc_cons (termCodeM t) (termsCodeM ts))
        (prf_eq_congr_succ (prf_lenc_termsCodeM ts))

theorem prf_nthc_termsCodeM : ∀ (ts : List Term) (k : Nat) (x : Term), ts[k]? = some x →
    Prf (nthc (termsCodeM ts) (numeralM k) =eq termCodeM x)
  | [],      k,     x, h => by simp at h
  | t :: ts, 0,     x, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      exact prf_nthc_zero (termCodeM t) (termsCodeM ts)
  | t :: ts, k + 1, x, h => by
      simp only [List.getElem?_cons_succ] at h
      exact prf_eq_trans (prf_nthc_succ (termCodeM t) (termsCodeM ts) (numeralM k))
        (prf_nthc_termsCodeM ts k x h)

theorem mem_of_getElem? : ∀ (L : List Term) (k : Nat) (x : Term), L[k]? = some x → List.Mem x L
  | [],      k,     x, h => by simp at h
  | e :: es, 0,     x, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      exact List.Mem.head _
  | e :: es, k + 1, x, h => by
      simp only [List.getElem?_cons_succ] at h
      exact List.Mem.tail _ (mem_of_getElem? es k x h)

/-! ### EL TESTIGO: **UNA** lista (la de codigos de TERMINO), y nada mas -/

mutual
def tcodes1 : Term → List Term
  | .var n     => [termCodeM (.var n)]
  | .func s ts => termCodeM (.func s ts) :: tcodes1s ts
def tcodes1s : List Term → List Term
  | []      => []
  | t :: ts => tcodes1 t ++ tcodes1s ts
end

theorem mem_self_tcodes1 (t : Term) : List.Mem (termCodeM t) (tcodes1 t) := by
  cases t with
  | var n     => simp only [tcodes1]; exact List.Mem.head _
  | func s ts => simp only [tcodes1]; exact List.Mem.head _

theorem mem_tcodes1s_of_mem : ∀ (ts : List Term) (t : Term), List.Mem t ts →
    List.Mem (termCodeM t) (tcodes1s ts)
  | [],      t, h => by cases h
  | u :: us, t, h => by
      simp only [tcodes1s]
      rcases List.mem_cons.mp h with rfl | h'
      · exact List.mem_append.mpr (Or.inl (mem_self_tcodes1 t))
      · exact List.mem_append.mpr (Or.inr (mem_tcodes1s_of_mem us t h'))

def CodeClosed (x : Term) : Prop :=
  (∀ c : Nat, liftTerm c x = x) ∧ (∀ (v : Nat) (s : Term), substTerm v s x = x)

theorem closed_termCodeM (t : Term) : CodeClosed (termCodeM t) :=
  ⟨fun c => liftTerm_termCodeM c t, fun v s => substTerm_termCodeM v s t⟩

mutual
theorem closed_mem_tcodes1 : ∀ (t x : Term), List.Mem x (tcodes1 t) → CodeClosed x
  | .var n, x, h => by
      simp only [tcodes1] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact closed_termCodeM (.var n)
      · cases h'
  | .func s ts, x, h => by
      simp only [tcodes1] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact closed_termCodeM (.func s ts)
      · exact closed_mem_tcodes1s ts x h'
theorem closed_mem_tcodes1s : ∀ (ts : List Term) (x : Term),
    List.Mem x (tcodes1s ts) → CodeClosed x
  | [], x, h => by simp only [tcodes1s] at h; cases h
  | t :: ts, x, h => by
      simp only [tcodes1s] at h
      rcases List.mem_append.mp h with hA | hB
      · exact closed_mem_tcodes1 t x hA
      · exact closed_mem_tcodes1s ts x hB
end

theorem liftTerm_objList (c : Nat) : ∀ (L : List Term),
    (∀ x : Term, List.Mem x L → liftTerm c x = x) → liftTerm c (objList L) = objList L
  | [],      _ => rfl
  | e :: es, h => by
      simp only [objList, cons, liftTerm, liftTerms, h e (List.Mem.head _),
        liftTerm_objList c es (fun x hx => h x (List.Mem.tail _ hx))]

theorem substTerm_objList (v : Nat) (s : Term) : ∀ (L : List Term),
    (∀ x : Term, List.Mem x L → substTerm v s x = x) → substTerm v s (objList L) = objList L
  | [],      _ => rfl
  | e :: es, h => by
      simp only [objList, cons, substTerm, substTerms, h e (List.Mem.head _),
        substTerm_objList v s es (fun x hx => h x (List.Mem.tail _ hx))]

theorem prf_lenc_objList : ∀ L : List Term,
    Prf (Formula.eq (lenc (objList L)) (numeralM L.length))
  | []      => prf_lenc_nil
  | e :: es =>
      prf_eq_trans (prf_lenc_cons e (objList es)) (prf_eq_congr_succ (prf_lenc_objList es))

theorem prf_nthc_objList : ∀ (L : List Term) (k : Nat) (x : Term), L[k]? = some x →
    Prf (Formula.eq (nthc (objList L) (numeralM k)) x)
  | [],      k,     x, h => by simp at h
  | e :: es, 0,     x, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      exact prf_nthc_zero e (objList es)
  | e :: es, k + 1, x, h => by
      simp only [List.getElem?_cons_succ] at h
      exact prf_eq_trans (prf_nthc_succ e (objList es) (numeralM k))
        (prf_nthc_objList es k x h)

theorem prf_In_objList : ∀ (L : List Term) (x : Term), List.Mem x L → Prf (In x (objList L))
  | [],      x, h => by cases h
  | e :: es, x, h => by
      rcases List.mem_cons.mp h with rfl | h'
      · exact prf_in_cons_head x (objList es)
      · exact prf_in_cons_tail e (prf_In_objList es x h')

/-! ### LA INDUCCION — **UNA sola** familia (con `wTs` habia DOS mutuas) -/

mutual
theorem okE1_T : ∀ (t : Term) (W : Term)
    (_hW : ∀ c : Nat, liftTerm c W = W) (_hWs : ∀ (v : Nat) (s : Term), substTerm v s W = W)
    (_ho : ∀ y : Term, List.Mem y (tcodes1 t) → Prf (In y W))
    (x : Term), List.Mem x (tcodes1 t) → Prf (isTermCodeE1 W x)
  | .var n, W, hW, hWs, ho, x, h => by
      simp only [tcodes1] at h
      rcases List.mem_cons.mp h with rfl | h'
      · show Prf (isTermCodeE1 W (termCodeM (.var n)))
        exact prf_isTermCodeE1_var W (numeralM n)
      · cases h'
  | .func s ts, W, hW, hWs, ho, x, h => by
      simp only [tcodes1] at h
      rcases List.mem_cons.mp h with rfl | h'
      · show Prf (isTermCodeE1 W (termCodeM (.func s ts)))
        refine prf_isTermCodeE1_func W (strCodeM s) (termsCodeM ts) ?_
        refine prf_argsIn_of_closed W (termsCodeM ts) ts.length (hW 0)
          (liftTerm_termsCodeM 0 ts) hWs (fun v s' => substTerm_termsCodeM v s' ts)
          (prf_lenc_termsCodeM ts) ?_
        intro k hk
        obtain ⟨u, hu⟩ : ∃ u, ts[k]? = some u := ⟨ts[k], getElem?_pos ts k hk⟩
        refine prf_congr_In_left (prf_eq_symm (prf_nthc_termsCodeM ts k u hu)) ?_
        refine ho (termCodeM u) ?_
        simp only [tcodes1]
        exact List.Mem.tail _ (mem_tcodes1s_of_mem ts u (mem_of_getElem? ts k u hu))
      · exact okE1_Ts ts W hW hWs
          (fun y hy => ho y (by simp only [tcodes1]; exact List.Mem.tail _ hy)) x h'
theorem okE1_Ts : ∀ (ts : List Term) (W : Term)
    (_hW : ∀ c : Nat, liftTerm c W = W) (_hWs : ∀ (v : Nat) (s : Term), substTerm v s W = W)
    (_ho : ∀ y : Term, List.Mem y (tcodes1s ts) → Prf (In y W))
    (x : Term), List.Mem x (tcodes1s ts) → Prf (isTermCodeE1 W x)
  | [], W, hW, hWs, ho, x, h => by simp only [tcodes1s] at h; cases h
  | t :: ts, W, hW, hWs, ho, x, h => by
      simp only [tcodes1s] at h
      rcases List.mem_append.mp h with hA | hB
      · exact okE1_T t W hW hWs
          (fun y hy => ho y (by
            simp only [tcodes1s]; exact List.mem_append.mpr (Or.inl hy))) x hA
      · exact okE1_Ts ts W hW hWs
          (fun y hy => ho y (by
            simp only [tcodes1s]; exact List.mem_append.mpr (Or.inr hy))) x hB
end

/-- **HITO (i) PARA LA VIA 2**: todo termino tiene testigo, y el testigo es **UNA SOLA
    LISTA** — `tcodes1 t`. Cero axiomas, cero simbolos nuevos. -/
theorem prf_isTC1_tcodes (t : Term) : Prf (isTC1 (objList (tcodes1 t)) (termCodeM t)) := by
  let L : List Term := tcodes1 t
  let W : Term := objList L
  have hWl : ∀ c : Nat, liftTerm c W = W := fun c =>
    liftTerm_objList c L (fun x hx => (closed_mem_tcodes1 t x hx).1 c)
  have hWs : ∀ (v : Nat) (s : Term), substTerm v s W = W := fun v s =>
    substTerm_objList v s L (fun x hx => (closed_mem_tcodes1 t x hx).2 v s)
  have horacle : ∀ y : Term, List.Mem y L → Prf (In y W) := fun y hy => prf_In_objList L y hy
  refine prf_and_intro ?_ (prf_In_objList L (termCodeM t) (mem_self_tcodes1 t))
  have hAI : wfAll1 W
      = Formula.forall (Formula.impl (lt (.var 0) (lenc W))
          (isTermCodeE1 W (nthc W (.var 0)))) := by
    simp only [wfAll1, wfAll1Body, lt, lenc, nthc, liftF_isTermCodeE1, liftTerm, liftTerms, hWl]
  rw [hAI]
  refine prf_bdAll_of_bound _ (lenc W) L.length ?_ (prf_lenc_objList L) ?_
  · simp only [substF_isTermCodeE1, nthc, substTerm, substTerms, hWs, if_true]
  · intro k hk
    obtain ⟨x, hx⟩ : ∃ x, L[k]? = some x := ⟨L[k], getElem?_pos L k hk⟩
    have hnode : Prf (isTermCodeE1 W x) :=
      okE1_T t W hWl hWs horacle x (mem_of_getElem? L k x hx)
    have : Prf (isTermCodeE1 W (nthc W (numeralM k))) :=
      prfH_nil_to_prf (PrfH_congr_isTermCodeE1
        (prf_to_prfH (prf_eq_symm (prf_nthc_objList L k x hx)) [])
        (prf_to_prfH hnode [])) rfl
    simpa only [substF_isTermCodeE1, nthc, substTerm, substTerms, hWs,
      substTerm_numeralM, if_true, reduceIte] using this


/-! ## §8 · PIEZAS NUEVAS

    Todo lo de aqui es PLANO (`Prf` de formulas objeto) y no toca `substfc`. -/

/-- Composicion de implicaciones en `PrfH` (combinador `B`). -/
theorem PrfH_impT {Γ : List Formula} {A B C : Formula}
    (h1 : PrfH Γ (Formula.impl A B)) (h2 : PrfH Γ (Formula.impl B C)) :
    PrfH Γ (Formula.impl A C) :=
  prfH_s_app (prfH_weaken h2) h1

/-! ### §8.1 · TODO OBJETO ES `nil` O UN `cons` — por `Prf.listInd` (regla del calculo) -/

def nilOrConsPred : Formula := lor (Formula.eq (.var 0) nil) (consOk (.var 0))

theorem nilOrConsPred_at (t : Term) :
    substFormula 0 t nilOrConsPred = lor (Formula.eq t nil) (consOk t) := by
  simp only [nilOrConsPred, consOk, lor, carc, cdrc, cons, nil, zero, substFormula, substTerm,
    substTerms, if_true]

/-- **`⊢ X ≐ nil ∨ X ≐ cons (carc X) (cdrc X)`** — analisis de casos de listas a nivel OBJETO,
    derivado de `prf_list_induction` (la HI ni se usa). -/
theorem prf_nil_or_cons (X : Term) : Prf (lor (Formula.eq X nil) (consOk X)) := by
  have key : Prf (Formula.forall nilOrConsPred) := by
    refine prf_list_induction nilOrConsPred ?base ?step
    · rw [nilOrConsPred_at]
      exact prf_orL (prf_refl nil)
    · refine Prf.gen _ (Prf.gen _ ?_)
      have hR : substFormula 0 (cons (.var 1) (.var 0))
            (liftFormula 2 (liftFormula 1 nilOrConsPred))
          = lor (Formula.eq (cons (.var 1) (.var 0)) nil) (consOk (cons (.var 1) (.var 0))) := by
        simp only [nilOrConsPred, consOk, lor, carc, cdrc, cons, nil, zero, liftFormula,
          substFormula, liftTerm, liftTerms, substTerm, substTerms, Nat.reduceAdd, Nat.reduceLT,
          Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceSub, reduceIte, if_true]
      rw [hR]
      exact prf_mp (Prf.incl (Prfᵢ.p1 _ _)) (prf_orR (prf_consOk_cons (.var 1) (.var 0)))
  have h := prf_spec key X
  rwa [nilOrConsPred_at] at h

/-! ### §8.2 · DE `In X w` + `wfAll1 w` SALE `isTermCodeE1 w X` (∃‑elim del indice) -/

theorem prf_isTermCodeE1_of_bdIn (w X : Term) :
    Prf (Formula.impl (boundedIn X w) (Formula.impl (wfAll1 w) (isTermCodeE1 w X))) := by
  refine prf_ex_elim_imp ?_
  simp only [liftFormula, liftF_wfAll1, liftF_isTermCodeE1]
  let W : Term := liftTerm 0 w
  let X' : Term := liftTerm 0 X
  let A : Formula := land (lt (.var 0) (liftTerm 0 (lenc w)))
    (Formula.eq (nthc (liftTerm 0 w) (.var 0)) (liftTerm 0 X))
  have hA : A = land (lt (.var 0) (lenc W)) (Formula.eq (nthc W (.var 0)) X') := by
    simp only [A, W, X', lenc, nthc, liftTerm, liftTerms]
  show PrfH [A] (Formula.impl (wfAll1 W) (isTermCodeE1 W X'))
  rw [hA]
  refine deduction_aux ?_ (wfAll1 W)
    [land (lt (.var 0) (lenc W)) (Formula.eq (nthc W (.var 0)) X')] rfl
  have hwf : PrfH [wfAll1 W, land (lt (.var 0) (lenc W)) (Formula.eq (nthc W (.var 0)) X')]
      (wfAll1 W) := PrfH.hyp _ _ (List.Mem.head _)
  have hbody : PrfH [wfAll1 W, land (lt (.var 0) (lenc W)) (Formula.eq (nthc W (.var 0)) X')]
      (land (lt (.var 0) (lenc W)) (Formula.eq (nthc W (.var 0)) X')) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  exact PrfH_congr_isTermCodeE1 (PrfH_and_elim_right hbody)
    (PrfH.mp _ _ _ (PrfH_inst_wfAll1 W (.var 0) hwf) (PrfH_and_elim_left hbody))

/-- **El nodo que esta en el testigo ES un codigo** (forma ECUACIONAL). -/
theorem prf_isTermCodeE1_of_In (w X : Term) :
    Prf (Formula.impl (land (wfAll1 w) (In X w)) (isTermCodeE1 w X)) := by
  refine prf_deduction ?_
  have hh : PrfH [land (wfAll1 w) (In X w)] (land (wfAll1 w) (In X w)) := prfH_hyp_self _
  have hbd : PrfH [land (wfAll1 w) (In X w)] (boundedIn X w) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_boundedIn_of_In X w) _) (PrfH_and_elim_right hh)
  exact PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (prf_isTermCodeE1_of_bdIn w X) _) hbd)
    (PrfH_and_elim_left hh)

/-! ### §8.3 · `argsIn` se DESCOMPONE en cabeza y cola -/

/-- La CABEZA de la lista de argumentos esta en el testigo. -/
theorem prf_argsIn_head (W X h t : Term) :
    Prf (Formula.impl (land (Formula.eq X (cons h t)) (argsIn W X)) (In h W)) := by
  refine prf_deduction ?_
  have hh : PrfH [land (Formula.eq X (cons h t)) (argsIn W X)]
      (land (Formula.eq X (cons h t)) (argsIn W X)) := prfH_hyp_self _
  have hX := PrfH_and_elim_left hh
  have hargs := PrfH_and_elim_right hh
  have hlen : PrfH [land (Formula.eq X (cons h t)) (argsIn W X)]
      (lenc X =eq succ (lenc t)) :=
    PrfH_eq_trans (PrfH_congr_lenc hX) (prf_to_prfH (prf_lenc_cons h t) _)
  have hlt : PrfH [land (Formula.eq X (cons h t)) (argsIn W X)] (lt zero (lenc X)) :=
    ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2 (PrfH_eq_symm hlen)
      (prf_to_prfH (prf_zero_lt_succ (lenc t)) _)
  have hin := PrfH.mp _ _ _ (PrfH_inst_argsIn W X zero hargs) hlt
  have hnth : PrfH [land (Formula.eq X (cons h t)) (argsIn W X)] (nthc X zero =eq h) :=
    PrfH_eq_trans (PrfH_congr_nthc_lst zero hX) (prf_to_prfH (prf_nthc_zero h t) _)
  exact PrfH_congr_In_left hnth hin

/-- La COLA de la lista de argumentos sigue teniendo todas sus posiciones en el testigo. -/
theorem prf_argsIn_tail (W X h t : Term) :
    Prf (Formula.impl (land (Formula.eq X (cons h t)) (argsIn W X)) (argsIn W t)) := by
  refine prf_mp (Prf.qconf (land (Formula.eq X (cons h t)) (argsIn W X)) (argsInBody W t))
    (Prf.gen _ ?_)
  have hgoal : Formula.impl (liftFormula 0 (land (Formula.eq X (cons h t)) (argsIn W X)))
        (argsInBody W t)
      = Formula.impl (land (Formula.eq (liftTerm 0 X) (cons (liftTerm 0 h) (liftTerm 0 t)))
            (argsIn (liftTerm 0 W) (liftTerm 0 X)))
          (Formula.impl (lt (.var 0) (lenc (liftTerm 0 t)))
            (In (nthc (liftTerm 0 t) (.var 0)) (liftTerm 0 W))) := by
    simp only [land, liftFormula, liftF_argsIn, argsInBody, cons, lenc, nthc, In, lt,
      liftTerm, liftTerms]
  rw [hgoal]
  refine prf_deduction (deduction_aux ?_ (lt (.var 0) (lenc (liftTerm 0 t)))
    [land (Formula.eq (liftTerm 0 X) (cons (liftTerm 0 h) (liftTerm 0 t)))
      (argsIn (liftTerm 0 W) (liftTerm 0 X))] rfl)
  have hh : PrfH [lt (.var 0) (lenc (liftTerm 0 t)),
      land (Formula.eq (liftTerm 0 X) (cons (liftTerm 0 h) (liftTerm 0 t)))
        (argsIn (liftTerm 0 W) (liftTerm 0 X))]
      (land (Formula.eq (liftTerm 0 X) (cons (liftTerm 0 h) (liftTerm 0 t)))
        (argsIn (liftTerm 0 W) (liftTerm 0 X))) := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hlt : PrfH [lt (.var 0) (lenc (liftTerm 0 t)),
      land (Formula.eq (liftTerm 0 X) (cons (liftTerm 0 h) (liftTerm 0 t)))
        (argsIn (liftTerm 0 W) (liftTerm 0 X))]
      (lt (.var 0) (lenc (liftTerm 0 t))) := PrfH.hyp _ _ (List.Mem.head _)
  have hX := PrfH_and_elim_left hh
  have hargs := PrfH_and_elim_right hh
  have hlen : PrfH _ (lenc (liftTerm 0 X) =eq succ (lenc (liftTerm 0 t))) :=
    PrfH_eq_trans (PrfH_congr_lenc hX)
      (prf_to_prfH (prf_lenc_cons (liftTerm 0 h) (liftTerm 0 t)) _)
  have hltS : PrfH _ (lt (succ (.var 0)) (lenc (liftTerm 0 X))) :=
    ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2 (PrfH_eq_symm hlen)
      (PrfH.mp _ _ _ (prf_to_prfH (prf_succ_lt_succ_of_lt (.var 0) (lenc (liftTerm 0 t))) _) hlt)
  have hin := PrfH.mp _ _ _
    (PrfH_inst_argsIn (liftTerm 0 W) (liftTerm 0 X) (succ (.var 0)) hargs) hltS
  have hnth : PrfH _ (nthc (liftTerm 0 X) (succ (.var 0)) =eq nthc (liftTerm 0 t) (.var 0)) :=
    PrfH_eq_trans (PrfH_congr_nthc_lst (succ (.var 0)) hX)
      (prf_to_prfH (prf_nthc_succ (liftTerm 0 h) (liftTerm 0 t) (.var 0)) _)
  exact PrfH_congr_In_left hnth hin

/-! ### §8.4 · Leibniz sobre `targetLiftsc` (la que falta; `targetLift` ya la tenia el §9) -/

theorem PrfH_congr_targetLiftsc {Γ : List Formula} {s s' : Term} (h : PrfH Γ (s =eq s'))
    (ha : PrfH Γ (targetLiftsc s)) : PrfH Γ (targetLiftsc s') := by
  have hS : ∀ u : Term, substFormula 0 u (targetLiftsc (.var 0)) = targetLiftsc u := by
    intro u
    simp only [substF_targetLiftsc, substTerm, if_true]
  exact (hS s') ▸ PrfH_leibniz_subst (A := targetLiftsc (.var 0)) h ((hS s) ▸ ha)

/-! ### §8.5 · EL DESCENSO ESTRICTO — `prf_cantor_mono` encadenado -/

/-- El TERCER campo de `funcc` (la lista de argumentos) es ESTRICTAMENTE menor que el nodo. -/
theorem prf_lt_arg_funcc (p b : Term) :
    Prf (lt b (cons (numeralM 1) (cons p (cons b nil)))) := by
  have h1 : Prf (lt b (cons b nil)) := prf_cantor_mono_left b nil
  have h2 : Prf (lt (cons b nil) (cons p (cons b nil))) := prf_cantor_mono_right p (cons b nil)
  have h3 : Prf (lt (cons p (cons b nil)) (cons (numeralM 1) (cons p (cons b nil)))) :=
    prf_cantor_mono_right (numeralM 1) (cons p (cons b nil))
  have h12 : Prf (lt b (cons p (cons b nil))) :=
    prf_mp (prf_mp (prf_lt_trans b (cons b nil) (cons p (cons b nil))) h1) h2
  exact prf_mp (prf_mp (prf_lt_trans b (cons p (cons b nil))
    (cons (numeralM 1) (cons p (cons b nil)))) h12) h3

/-! ### §8.6 · LA HIPOTESIS DE INDUCCION FUERTE, INSTANCIADA -/

theorem PSI0_shape :
    liftFormula 0 (PSI PHI) = Formula.forall (Formula.impl (lt (.var 0) (.var 2)) PHI) := by
  simp only [PSI, liftFormula, lt, liftTerm, liftTerms, Nat.reduceAdd, Nat.reduceLT,
    Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceSub, reduceIte, hPHI]

/-- De la HI fuerte (`↑(PSI Φ)`, con el codigo en `#1`) sale, para cada `b`,
    la implicacion OBJETO `b < #1 ⇒ Φ(b)[w := W]`. -/
theorem ih_of_psi {Γ : List Formula} (W b : Term) (hpsi : PrfH Γ (liftFormula 0 (PSI PHI))) :
    PrfH Γ (Formula.impl (lt b (.var 1)) (bodyF W b)) := by
  rw [PSI0_shape] at hpsi
  have h1 := PrfH_spec hpsi b
  have hshape : substFormula 0 b (Formula.impl (lt (.var 0) (.var 2)) PHI)
      = Formula.impl (lt b (.var 1)) (Formula.forall (bodyF (.var 0) (liftTerm 0 b))) := by
    simp only [substFormula, lt, substTerm, substTerms, PHI_at, Nat.reduceAdd, Nat.reduceLT,
      Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceSub, reduceIte, if_true]
  rw [hshape] at h1
  have hq : Prf (Formula.impl (Formula.forall (bodyF (.var 0) (liftTerm 0 b))) (bodyF W b)) := by
    have hqq := Prf.incl (Prfᵢ.q1 (bodyF (.var 0) (liftTerm 0 b)) W)
    rwa [substF_bodyF, FOL.substTerm_liftTerm, substTerm, if_pos rfl] at hqq
  exact PrfH_impT h1 (prf_to_prfH hq Γ)

/-! ### §8.7 · EL PASO DE LA INDUCCION FUERTE -/

theorem step_PHI : Prf (Formula.forall (Formula.impl (PSI PHI) PHI)) := by
  refine Prf.gen _ ?_
  refine prf_mp (Prf.qconf (PSI PHI) (bodyF (.var 0) (.var 1))) (Prf.gen _ ?_)
  refine prf_deduction ?_
  show PrfH [liftFormula 0 (PSI PHI)] (bodyF (.var 0) (.var 1))
  unfold bodyF
  refine PrfH_and_intro ?_ ?_
  · -- PARTE 1 · el NODO
    refine deduction_aux ?_ (isTC1 (.var 0) (.var 1)) [liftFormula 0 (PSI PHI)] rfl
    have hitc : PrfH [isTC1 (.var 0) (.var 1), liftFormula 0 (PSI PHI)]
        (isTC1 (.var 0) (.var 1)) := PrfH.hyp _ _ (List.Mem.head _)
    have hpsi : PrfH [isTC1 (.var 0) (.var 1), liftFormula 0 (PSI PHI)]
        (liftFormula 0 (PSI PHI)) := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
    have hwf : PrfH [isTC1 (.var 0) (.var 1), liftFormula 0 (PSI PHI)]
        (wfAll1 (.var 0)) := PrfH_and_elim_left hitc
    have hin : PrfH [isTC1 (.var 0) (.var 1), liftFormula 0 (PSI PHI)]
        (In (.var 1) (.var 0)) := PrfH_and_elim_right hitc
    have hE : PrfH [isTC1 (.var 0) (.var 1), liftFormula 0 (PSI PHI)]
        (lor (shapeUn (.var 1) 0)
          (land (shapeBin (.var 1) 1)
            (argsIn (.var 0) (nthc (.var 1) (numeralM 2))))) :=
      PrfH.mp _ _ _ (prf_to_prfH (prf_isTermCodeE1_of_In (.var 0) (.var 1)) _)
        (PrfH_and_intro hwf hin)
    refine PrfH_or_elim hE ?_ ?_
    · exact PrfH.mp _ _ _ (prf_to_prfH (refl_shapeUn_imp (.var 1)) _)
        (PrfH.hyp _ _ (List.Mem.head _))
    · have hh : PrfH [land (shapeBin (.var 1) 1) (argsIn (.var 0) (nthc (.var 1) (numeralM 2))),
          isTC1 (.var 0) (.var 1), liftFormula 0 (PSI PHI)]
          (land (shapeBin (.var 1) 1) (argsIn (.var 0) (nthc (.var 1) (numeralM 2)))) :=
        PrfH.hyp _ _ (List.Mem.head _)
      have hitc2 : PrfH [land (shapeBin (.var 1) 1)
            (argsIn (.var 0) (nthc (.var 1) (numeralM 2))),
          isTC1 (.var 0) (.var 1), liftFormula 0 (PSI PHI)] (isTC1 (.var 0) (.var 1)) :=
        PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
      have hpsi2 : PrfH [land (shapeBin (.var 1) 1)
            (argsIn (.var 0) (nthc (.var 1) (numeralM 2))),
          isTC1 (.var 0) (.var 1), liftFormula 0 (PSI PHI)] (liftFormula 0 (PSI PHI)) :=
        PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
      have hsb := PrfH_and_elim_left hh
      have hargs := PrfH_and_elim_right hh
      have hwf2 := PrfH_and_elim_left hitc2
      have hltb : PrfH _ (lt (nthc (.var 1) (numeralM 2)) (.var 1)) :=
        ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2 (PrfH_eq_symm hsb)
          (prf_to_prfH (prf_lt_arg_funcc (nthc (.var 1) (numeralM 1))
            (nthc (.var 1) (numeralM 2))) _)
      have hbody := PrfH.mp _ _ _
        (ih_of_psi (.var 0) (nthc (.var 1) (numeralM 2)) hpsi2) hltb
      have htls : PrfH _ (targetLiftsc (nthc (.var 1) (numeralM 2))) :=
        PrfH.mp _ _ _ (PrfH_and_elim_right hbody) (PrfH_and_intro hwf2 hargs)
      exact PrfH.mp _ _ _ (prf_to_prfH (refl_shapeBin_imp (.var 1)) _)
        (PrfH_and_intro hsb htls)
  · -- PARTE 2 · la LISTA de argumentos
    refine deduction_aux ?_ (land (wfAll1 (.var 0)) (argsIn (.var 0) (.var 1)))
      [liftFormula 0 (PSI PHI)] rfl
    have hh : PrfH [land (wfAll1 (.var 0)) (argsIn (.var 0) (.var 1)),
        liftFormula 0 (PSI PHI)]
        (land (wfAll1 (.var 0)) (argsIn (.var 0) (.var 1))) := PrfH.hyp _ _ (List.Mem.head _)
    have hpsi : PrfH [land (wfAll1 (.var 0)) (argsIn (.var 0) (.var 1)),
        liftFormula 0 (PSI PHI)] (liftFormula 0 (PSI PHI)) :=
      PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
    have hnc : PrfH [land (wfAll1 (.var 0)) (argsIn (.var 0) (.var 1)),
        liftFormula 0 (PSI PHI)]
        (lor (Formula.eq (.var 1) nil) (consOk (.var 1))) :=
      prf_to_prfH (prf_nil_or_cons (.var 1)) _
    refine PrfH_or_elim hnc ?_ ?_
    · exact PrfH_congr_targetLiftsc (PrfH_eq_symm (PrfH.hyp _ _ (List.Mem.head _)))
        (prf_to_prfH refl_lista_nil _)
    · have hcons : PrfH [consOk (.var 1),
          land (wfAll1 (.var 0)) (argsIn (.var 0) (.var 1)), liftFormula 0 (PSI PHI)]
          (Formula.eq (.var 1) (cons (carc (.var 1)) (cdrc (.var 1)))) :=
        PrfH.hyp _ _ (List.Mem.head _)
      have hh3 : PrfH [consOk (.var 1),
          land (wfAll1 (.var 0)) (argsIn (.var 0) (.var 1)), liftFormula 0 (PSI PHI)]
          (land (wfAll1 (.var 0)) (argsIn (.var 0) (.var 1))) :=
        PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
      have hpsi3 : PrfH [consOk (.var 1),
          land (wfAll1 (.var 0)) (argsIn (.var 0) (.var 1)), liftFormula 0 (PSI PHI)]
          (liftFormula 0 (PSI PHI)) :=
        PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
      have hwf3 := PrfH_and_elim_left hh3
      have hargs3 := PrfH_and_elim_right hh3
      have hinh : PrfH _ (In (carc (.var 1)) (.var 0)) :=
        PrfH.mp _ _ _ (prf_to_prfH (prf_argsIn_head (.var 0) (.var 1)
          (carc (.var 1)) (cdrc (.var 1))) _) (PrfH_and_intro hcons hargs3)
      have hargst : PrfH _ (argsIn (.var 0) (cdrc (.var 1))) :=
        PrfH.mp _ _ _ (prf_to_prfH (prf_argsIn_tail (.var 0) (.var 1)
          (carc (.var 1)) (cdrc (.var 1))) _) (PrfH_and_intro hcons hargs3)
      have hlth : PrfH _ (lt (carc (.var 1)) (.var 1)) :=
        ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2 (PrfH_eq_symm hcons)
          (prf_to_prfH (prf_cantor_mono_left (carc (.var 1)) (cdrc (.var 1))) _)
      have hltt : PrfH _ (lt (cdrc (.var 1)) (.var 1)) :=
        ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2 (PrfH_eq_symm hcons)
          (prf_to_prfH (prf_cantor_mono_right (carc (.var 1)) (cdrc (.var 1))) _)
      have hbh := PrfH.mp _ _ _ (ih_of_psi (.var 0) (carc (.var 1)) hpsi3) hlth
      have hbt := PrfH.mp _ _ _ (ih_of_psi (.var 0) (cdrc (.var 1)) hpsi3) hltt
      have htlh : PrfH _ (targetLift (carc (.var 1))) :=
        PrfH.mp _ _ _ (PrfH_and_elim_left hbh) (PrfH_and_intro hwf3 hinh)
      have htlt : PrfH _ (targetLiftsc (cdrc (.var 1))) :=
        PrfH.mp _ _ _ (PrfH_and_elim_right hbt) (PrfH_and_intro hwf3 hargst)
      have hcc : PrfH _ (targetLiftsc (cons (carc (.var 1)) (cdrc (.var 1)))) :=
        PrfH.mp _ _ _ (prf_to_prfH (refl_lista_cons_imp (carc (.var 1)) (cdrc (.var 1))) _)
          (PrfH_and_intro htlh htlt)
      exact PrfH_congr_targetLiftsc (PrfH_eq_symm hcons) hcc

/-! ## §9 · EL DESCENSO -/

theorem prf_bodyF (W X : Term) : Prf (bodyF W X) :=
  PHI_inst X W (prf_strong_induction PHI hPHI step_PHI X)

/-- **EL DESCENSO** — `w` y `s` ABSTRACTOS, cero axiomas nuevos. -/
theorem DESCENSO (w s : Term) (h : Prf (isTC1 w s)) : Prf (targetLift s) :=
  prf_mp (prf_and_elim_left (prf_bodyF w s)) h

/-- **EL DESCENSO SOBRE LISTAS** (la gemela). -/
theorem DESCENSO_lista (w b : Term) (hwf : Prf (wfAll1 w)) (hargs : Prf (argsIn w b)) :
    Prf (targetLiftsc b) :=
  prf_mp (prf_and_elim_right (prf_bodyF w b)) (prf_and_intro hwf hargs)

/-! ## §10 · NO VACUIDAD — la hipotesis del DESCENSO la cumple TODO termino REAL

    `prf_isTC1_tcodes` (Hito (i), copiado literal en §7) da el testigo explicito. Si el
    enunciado del §9 fuese vacio, esto no compilaria. -/

/-- El DESCENSO, aplicado al testigo REAL de un termino cualquiera. -/
theorem descenso_no_vacuo (t : Term) : Prf (targetLift (termCodeM t)) :=
  DESCENSO (objList (tcodes1 t)) (termCodeM t) (prf_isTC1_tcodes t)

/-- Y la gemela de listas, con el mismo testigo (la lista de argumentos de un `funcc`). -/
theorem descenso_lista_no_vacuo (s : String) (ts : List Term) :
    Prf (targetLiftsc (termsCodeM ts)) := by
  have h := prf_isTC1_tcodes (.func s ts)
  have hWl : ∀ c : Nat, liftTerm c (objList (tcodes1 (.func s ts)))
      = objList (tcodes1 (.func s ts)) := fun c =>
    liftTerm_objList c _ (fun x hx => (closed_mem_tcodes1 (.func s ts) x hx).1 c)
  have hWs : ∀ (v : Nat) (u : Term), substTerm v u (objList (tcodes1 (.func s ts)))
      = objList (tcodes1 (.func s ts)) := fun v u =>
    substTerm_objList v u _ (fun x hx => (closed_mem_tcodes1 (.func s ts) x hx).2 v u)
  refine DESCENSO_lista (objList (tcodes1 (.func s ts))) (termsCodeM ts)
    (prf_and_elim_left h) ?_
  refine prf_argsIn_of_closed _ (termsCodeM ts) ts.length (hWl 0)
    (liftTerm_termsCodeM 0 ts) hWs (fun v u => substTerm_termsCodeM v u ts)
    (prf_lenc_termsCodeM ts) ?_
  intro k hk
  obtain ⟨u, hu⟩ : ∃ u, ts[k]? = some u := ⟨ts[k], getElem?_pos ts k hk⟩
  refine prf_congr_In_left (prf_eq_symm (prf_nthc_termsCodeM ts k u hu)) ?_
  refine prf_In_objList (tcodes1 (.func s ts)) (termCodeM u) ?_
  simp only [tcodes1]
  exact List.Mem.tail _ (mem_tcodes1s_of_mem ts u (mem_of_getElem? ts k u hu))

end DescFuerte

#print axioms DescFuerte.DESCENSO
#print axioms DescFuerte.DESCENSO_lista
#print axioms DescFuerte.descenso_no_vacuo
#print axioms DescFuerte.descenso_lista_no_vacuo
#print axioms DescFuerte.prf_bodyF
#print axioms DescFuerte.PHI_inst
#print axioms DescFuerte.ih_of_psi
#print axioms DescFuerte.prf_isTC1_tcodes
#print axioms DescFuerte.step_PHI
#print axioms DescFuerte.hPHI
#print axioms DescFuerte.prf_nil_or_cons
#print axioms DescFuerte.prf_isTermCodeE1_of_In
#print axioms DescFuerte.prf_argsIn_head
#print axioms DescFuerte.prf_argsIn_tail
#print axioms DescFuerte.prf_lt_arg_funcc

-- CONTROL 1 · los ENUNCIADOS, literales
#print DescFuerte.DESCENSO
#print DescFuerte.DESCENSO_lista
#print DescFuerte.descenso_no_vacuo
#print DescFuerte.targetLift
#print DescFuerte.isTC1
#print DescFuerte.PHI

-- CONTROL 2 · el objetivo NO es una reflexividad disfrazada (control negativo del sondeo)
example (s : Term) : True := by
  fail_if_success
    exact (rfl : DescFuerte.liftcT (termCode zero) (tcFn s) = tcFn (liftc zero s))
  trivial

/-! ############################################################################
    ##  CRITICA ADVERSARIAL  (todo lo de arriba es COPIA LITERAL del entregable)
    ############################################################################ -/

namespace DescFuerte

/-! ### C1 · ABSTRACCION: `w` y `s` son variables LIBRES, no instancias -/

theorem crit_abstracto : ∀ (w s : Term), Prf (isTC1 w s) → Prf (targetLift s) := DESCENSO

theorem crit_abstracto_lista :
    ∀ (w b : Term), Prf (wfAll1 w) → Prf (argsIn w b) → Prf (targetLiftsc b) := DESCENSO_lista

/-! ### C2 · EL PUENTE AL CONSUMIDOR `Paso2CasoForall.lean:507`, tipado a mano -/

theorem crit_puente_rfl (s : Term) :
    targetLift s
      = provFromCode (eqc (liftcT (termCode zero) (tcFn s)) (tcFn (liftc zero s))) := rfl

/-- El `hLift` que pide `paso2_caso_forall (v s f : Term)`, con `s` ABSTRACTO. -/
theorem crit_hLift_abstracto (w s : Term) (h : Prf (isTC1 w s)) :
    Prf (provFromCode (eqc (liftcT (termCode zero) (tcFn s)) (tcFn (liftc zero s)))) :=
  DESCENSO w s h

/-! ### C3 · SATISFACIBILIDAD con simbolos de funcion REALES -/

theorem crit_real_f : Prf (targetLift (termCodeM (.func "f" [.var 0]))) :=
  descenso_no_vacuo (.func "f" [.var 0])

theorem crit_real_f_directo : Prf (targetLift (termCodeM (.func "f" [.var 0]))) :=
  DESCENSO (objList (tcodes1 (.func "f" [.var 0]))) (termCodeM (.func "f" [.var 0]))
    (prf_isTC1_tcodes (.func "f" [.var 0]))

/-- Anidado y con DOS argumentos: `plus (S #0) #1`. -/
theorem crit_real_anidado :
    Prf (targetLift (termCodeM (.func "plus" [.func "S" [.var 0], .var 1]))) :=
  descenso_no_vacuo _

theorem crit_real_lista :
    Prf (targetLiftsc (termsCodeM [.func "S" [.var 0], .var 1])) :=
  descenso_lista_no_vacuo "plus" _

/-! ### C4 · ¿ES LA PREMISA UNA RESTRICCION REAL?  Sí: RECHAZA codigos de FORMULA.
    Si `isTC1 w s` fuese satisfacible por cualquier cosa, el DESCENSO seria trivial.
    Aqui se refuta `implc` (tag 5), que NO es codigo de termino. -/

theorem crit_num_ne : ∀ (m n : Nat), m ≠ n →
    Prf (Formula.impl (Formula.eq (numeralM m) (numeralM n)) Formula.bottom)
  | 0,     0,     h => absurd rfl h
  | 0,     _ + 1, _ =>
      prf_deduction (PrfH.mp _ _ _ (prf_to_prfH (prf_succ_ne_zero (numeralM _)) _)
        (PrfH_eq_symm (prfH_hyp_self _)))
  | m + 1, 0,     _ => prf_succ_ne_zero (numeralM m)
  | m + 1, n + 1, h =>
      impT (prf_succ_inj (numeralM m) (numeralM n)) (crit_num_ne m n (fun e => h (by omega)))

theorem crit_shapeUn_tag (X : Term) (k : Nat) :
    Prf (Formula.impl (shapeUn X k) (nthc X zero =eq numeralM k)) := by
  refine prf_deduction ?_
  have hs : PrfH [shapeUn X k]
      (Formula.eq X (cons (numeralM k) (cons (nthc X (numeralM 1)) nil))) := prfH_hyp_self _
  exact PrfH_eq_trans (PrfH_congr_nthc_lst zero hs)
    (prf_to_prfH (prf_nthc_zero (numeralM k) (cons (nthc X (numeralM 1)) nil)) _)

theorem crit_shapeBin_tag (X : Term) (k : Nat) :
    Prf (Formula.impl (shapeBin X k) (nthc X zero =eq numeralM k)) := by
  refine prf_deduction ?_
  have hs : PrfH [shapeBin X k]
      (Formula.eq X (cons (numeralM k)
        (cons (nthc X (numeralM 1)) (cons (nthc X (numeralM 2)) nil)))) := prfH_hyp_self _
  exact PrfH_eq_trans (PrfH_congr_nthc_lst zero hs)
    (prf_to_prfH (prf_nthc_zero (numeralM k)
      (cons (nthc X (numeralM 1)) (cons (nthc X (numeralM 2)) nil))) _)

theorem crit_isTermCodeE1_rechaza_implc (W a b : Term) :
    Prf (Formula.impl (isTermCodeE1 W (implc a b)) Formula.bottom) := by
  have h5 : Prf (nthc (implc a b) zero =eq numeralM 5) :=
    prf_nthc_zero (numeralM 5) (cons a (cons b nil))
  refine prf_deduction ?_
  have hE : PrfH [isTermCodeE1 W (implc a b)]
      (lor (shapeUn (implc a b) 0)
        (land (shapeBin (implc a b) 1)
          (argsIn W (nthc (implc a b) (numeralM 2))))) := prfH_hyp_self _
  refine PrfH_or_elim hE ?_ ?_
  · have hyp : PrfH [shapeUn (implc a b) 0, isTermCodeE1 W (implc a b)]
        (shapeUn (implc a b) 0) := PrfH.hyp _ _ (List.Mem.head _)
    have h0 : PrfH [shapeUn (implc a b) 0, isTermCodeE1 W (implc a b)]
        (nthc (implc a b) zero =eq numeralM 0) :=
      PrfH.mp _ _ _ (prf_to_prfH (crit_shapeUn_tag (implc a b) 0) _) hyp
    exact PrfH.mp _ _ _ (prf_to_prfH (crit_num_ne 0 5 (by decide)) _)
      (PrfH_eq_trans (PrfH_eq_symm h0) (prf_to_prfH h5 _))
  · have hyp : PrfH [land (shapeBin (implc a b) 1)
          (argsIn W (nthc (implc a b) (numeralM 2))), isTermCodeE1 W (implc a b)]
        (land (shapeBin (implc a b) 1)
          (argsIn W (nthc (implc a b) (numeralM 2)))) := PrfH.hyp _ _ (List.Mem.head _)
    have h1 : PrfH [land (shapeBin (implc a b) 1)
          (argsIn W (nthc (implc a b) (numeralM 2))), isTermCodeE1 W (implc a b)]
        (nthc (implc a b) zero =eq numeralM 1) :=
      PrfH.mp _ _ _ (prf_to_prfH (crit_shapeBin_tag (implc a b) 1) _)
        (PrfH_and_elim_left hyp)
    exact PrfH.mp _ _ _ (prf_to_prfH (crit_num_ne 1 5 (by decide)) _)
      (PrfH_eq_trans (PrfH_eq_symm h1) (prf_to_prfH h5 _))

/-- **NINGUN testigo `W` admite `implc a b`**: la premisa del DESCENSO discrimina. -/
theorem crit_isTC1_rechaza_implc (W a b : Term) :
    Prf (Formula.impl (isTC1 W (implc a b)) Formula.bottom) := by
  refine prf_deduction ?_
  have hh : PrfH [isTC1 W (implc a b)] (land (wfAll1 W) (In (implc a b) W)) := prfH_hyp_self _
  exact PrfH.mp _ _ _ (prf_to_prfH (crit_isTermCodeE1_rechaza_implc W a b) _)
    (PrfH.mp _ _ _ (prf_to_prfH (prf_isTermCodeE1_of_In W (implc a b)) _) hh)

end DescFuerte

#print axioms DescFuerte.crit_abstracto
#print axioms DescFuerte.crit_abstracto_lista
#print axioms DescFuerte.crit_hLift_abstracto
#print axioms DescFuerte.crit_real_f
#print axioms DescFuerte.crit_real_anidado
#print axioms DescFuerte.crit_real_lista
#print axioms DescFuerte.crit_isTC1_rechaza_implc

#print DescFuerte.crit_abstracto
#print DescFuerte.crit_hLift_abstracto

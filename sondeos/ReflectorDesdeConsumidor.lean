/-
# VIA 3 — DESDE EL CONSUMIDOR HACIA ATRAS.

El consumidor final es `sondeos/Paso2CasoForall.lean:505`, `paso2_caso_forall`, cuya UNICA
hipotesis sin descargar es

    hLift : Prf (provFromCode (eqc (liftcT (termCode zero) (tcFn s)) (tcFn (liftc zero s))))

Pregunta: ¿que forma MINIMA del reflector hace falta para producir ese `hLift`?

Fichero AUTOCONTENIDO (`import ROBINSON_PlusPlus.Meta` y nada mas). Las definiciones que hacen
falta van COPIADAS de `sondeos/Paso2CasoForall.lean` (§1) y de `Probe/CritLift_sinwts.lean` (§1).

## RESPUESTA MEDIDA

**NO HAY MURO NUEVO. El `∀` anidado NUNCA se toca en la cara punteada.**

Lo que `hLift` pide de la cara PUNTEADA es, exactamente y nada mas, cuatro ECUACIONES DE CODIGO
LIBRES DE CUANTIFICADOR (§4/§5) mas la reflexion del ATOMO `<` (`pcc_lt_tracked`, ya en
produccion). Ni un `bdAllCode`, ni un `∀` acotado, ni la imagen punteada de `wfAll1`/`argsIn`.

Lo que pide del PREDICADO es solo su forma ECUACIONAL, **a nivel PLANO**:
`X ≐ varc a` / `X ≐ funcc p b` — que es literalmente `shapeUn X 0` / `shapeBin X 1` (§9, por
`rfl`). `argsIn` **no se usa en el reflector**: se descarta en la eliminacion del `∧` (§10).

Lo que queda sin descargar es UNA sola cosa, y es PLANA: el **DESCENSO** (§11).
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

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

namespace ReflConsumidor

/-! ## §1 · Los constructores de codigo (DEFINICIONES; ninguna ecuacion suya se postula) -/

def liftcT (c t : Term) : Term := funcc (strCode "liftc") (cons c (cons t nil))
def liftscT (c ts : Term) : Term := funcc (strCode "liftsc") (cons c (cons ts nil))

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

/-! ## §2 · EL OBJETIVO EXACTO — copiado del enunciado de `paso2_caso_forall` -/

/-- La hipotesis sin descargar de `sondeos/Paso2CasoForall.lean:507`, literal. -/
def targetLift (s : Term) : Formula :=
  provFromCode (eqc (liftcT (termCode zero) (tcFn s)) (tcFn (liftc zero s)))

/-- CONTROL NEGATIVO: no es una reflexividad disfrazada. -/
example (s : Term) : True := by
  fail_if_success
    exact (rfl : liftcT (termCode zero) (tcFn s) = tcFn (liftc zero s))
  trivial

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

/-! ## §7 · LAS CUATRO CLAUSULAS DE LA RECURSION — el esqueleto entero de `hLift`

    `targetLift s` es LITERALMENTE la hipotesis sin descargar de `paso2_caso_forall`.
    `targetLiftsc b` es su companera sobre listas de argumentos.

    ⚠️ Observese el ENUNCIADO de las cuatro: la guarda entra **SOLO como una ecuacion PLANA**
    (`s ≐ varc a`, `s ≐ funcc p b`). Ni `wfAll1`, ni `argsIn`, ni `In`, ni ningun `bdAllCode`
    aparecen en ninguna de ellas. -/

def targetLiftsc (b : Term) : Formula :=
  provFromCode (eqc (liftscT (termCode zero) (tcFn b)) (tcFn (liftsc zero b)))

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

/-! ## §8 · NO VACUIDAD / COMPLETITUD DEL ESQUEMA — las cuatro clausulas CIERRAN el objetivo
       para todo codigo de termino GENUINO (`termCode t`), por recursion META.

    No es el teorema que hace falta (ahi `s` es abstracto), pero comprueba que las cuatro
    clausulas son un CUBRIMIENTO COMPLETO: no falta ninguna forma. -/

mutual
theorem refl_termCode : ∀ t : Term, Prf (targetLift (termCode t))
  | .var n     => refl_caso_varc (termCode (.var n)) (numeral n) (prf_refl _)
  | .func f ts =>
      refl_caso_funcc (termCode (.func f ts)) (strCode f) (termsCode ts)
        (prf_refl _) (refl_termsCode ts)
theorem refl_termsCode : ∀ ts : List Term, Prf (targetLiftsc (termsCode ts))
  | []      => refl_lista_nil
  | t :: ts => refl_lista_cons (termCode t) (termsCode ts) (refl_termCode t) (refl_termsCode ts)
end

/-! ## §9 · LA FORMA ECUACIONAL DE LA GUARDA ES *EXACTAMENTE* LO QUE PIDEN LAS CLAUSULAS

    `shapeUn X 0` y `shapeBin X 1` de `Probe/CritLift_sinwts.lean` son, **por `rfl`**,
    las dos ecuaciones que consumen `refl_caso_varc` / `refl_caso_funcc`. -/

def shapeUn (X : Term) (k : Nat) : Formula :=
  Formula.eq X (cons (numeralM k) (cons (nthc X (numeralM 1)) nil))
def shapeBin (X : Term) (k : Nat) : Formula :=
  Formula.eq X (cons (numeralM k)
    (cons (nthc X (numeralM 1)) (cons (nthc X (numeralM 2)) nil)))

theorem shapeUn0_es_varc (X : Term) :
    shapeUn X 0 = Formula.eq X (varc (nthc X (numeralM 1))) := rfl
theorem shapeBin1_es_funcc (X : Term) :
    shapeBin X 1 = Formula.eq X (funcc (nthc X (numeralM 1)) (nthc X (numeralM 2))) := rfl

/-! ### La guarda llega como HIPOTESIS OBJETO, no como `Prf`: el transporte de Leibniz -/

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

/-! ## §10 · EL PREDICADO SIN‑`wTs` ENTERO, CONTRA EL OBJETIVO — la MEDIDA

    Copia LITERAL de `Probe/CritLift_sinwts.lean:109‑135` del predicado de un nodo. -/

def argsInBody (wT Y : Term) : Formula :=
  Formula.impl (lt (.var 0) (liftTerm 0 (lenc Y)))
    (In (nthc (liftTerm 0 Y) (.var 0)) (liftTerm 0 wT))
def argsIn (wT Y : Term) : Formula := Formula.forall (argsInBody wT Y)

def isTermCodeE1 (wT X : Term) : Formula :=
  lor (shapeUn X 0) (land (shapeBin X 1) (argsIn wT (nthc X (numeralM 2))))

theorem impT {A B C : Formula} (h1 : Prf (A ⇒ B)) (h2 : Prf (B ⇒ C)) : Prf (A ⇒ C) := by
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH h2 _) (PrfH.mp _ _ _ (prf_to_prfH h1 _) (prfH_hyp_self _))

theorem prf_or_elim_imp {A B C : Formula} (h1 : Prf (A ⇒ C)) (h2 : Prf (B ⇒ C)) :
    Prf (lor A B ⇒ C) := by
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (PrfH.mp _ _ _
    (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.j3 A B C)) (prfH_hyp_self _))
    (prf_to_prfH h1 _)) (prf_to_prfH h2 _)

/-- **EL RESULTADO CENTRAL DE ESTE FICHERO.**

    El predicado `isTermCodeE1 w X` de la via sin‑`wTs`, contra el objetivo `targetLift X`:

        ⊢ isTermCodeE1 w X ⇒ (targetLiftsc (nthc X 2̄) ⇒ targetLift X)

    * La `∨` de los dos disyuntos, su forma ECUACIONAL y el `land`: **usados**.
    * `argsIn w (nthc X 2̄)` — el `∀` ACOTADO ANIDADO: **NO se usa**. Se descarta en la
      eliminacion del `∧`. Su unico papel es alimentar el DESCENSO (garantizar que los hijos
      vuelven a ser codigos), es decir producir la premisa `targetLiftsc (nthc X 2̄)`.
    * Ni un solo `bdAllCode` en la cara punteada: el consecuente es una ecuacion de codigo. -/
theorem refl_isTermCodeE1_imp (w X : Term) :
    Prf (Formula.impl (isTermCodeE1 w X)
      (Formula.impl (targetLiftsc (nthc X (numeralM 2))) (targetLift X))) := by
  unfold isTermCodeE1
  refine prf_or_elim_imp ?_ ?_
  · exact impT (refl_shapeUn_imp X)
      (Prf.incl (Prf₀.p1 (targetLift X) (targetLiftsc (nthc X (numeralM 2)))))
  · refine prf_deduction (deduction_aux ?_ (targetLiftsc (nthc X (numeralM 2)))
      [land (shapeBin X 1) (argsIn w (nthc X (numeralM 2)))] rfl)
    have hT : PrfH [targetLiftsc (nthc X (numeralM 2)),
        land (shapeBin X 1) (argsIn w (nthc X (numeralM 2)))]
        (targetLiftsc (nthc X (numeralM 2))) := PrfH.hyp _ _ (List.Mem.head _)
    have hB : PrfH [targetLiftsc (nthc X (numeralM 2)),
        land (shapeBin X 1) (argsIn w (nthc X (numeralM 2)))]
        (land (shapeBin X 1) (argsIn w (nthc X (numeralM 2)))) :=
      PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
    exact PrfH.mp _ _ _ (prf_to_prfH (refl_shapeBin_imp X) _)
      (PrfH_and_intro (PrfH_and_elim_left hB) hT)

/-! ## §11 · EL RESIDUO, con nombre y enunciado exactos.

    Lo unico que NO se descarga aqui es el **DESCENSO**: pasar de «cada hijo es de nuevo un
    codigo con testigo» a la premisa `targetLiftsc (nthc X 2̄)`. En enunciado:

    ```lean
    DESCENSO :
      ∀ w X, Prf (isTC1 w X)                       -- wfAll1 w ∧ In X w
           → Prf (targetLiftsc (nthc X (numeralM 2)))
    ```

    y es una recursion BIEN FUNDADA sobre el valor del codigo (`prf_strong_induction` +
    `prf_cantor_mono_left/right`, ambos en produccion), combinada con `prf_list_induction`
    para recorrer la lista de argumentos —— con `refl_lista_nil` / `refl_lista_cons_imp` como
    base y paso, que YA estan cerrados aqui.

    ⚠️ Ese residuo es **enteramente PLANO** (`Prf` de formulas objeto). Ninguna de sus piezas
    pide la imagen PUNTEADA de `wfAll1`, de `argsIn` ni de `isTC1`. -/

end ReflConsumidor

#print axioms ReflConsumidor.refl_isTermCodeE1_imp
#print axioms ReflConsumidor.refl_caso_funcc_imp
#print axioms ReflConsumidor.refl_shapeBin_imp
#print axioms ReflConsumidor.refl_lista_cons_imp
#print axioms ReflConsumidor.refl_termCode
#print axioms ReflConsumidor.refl_termsCode
#print axioms ReflConsumidor.shapeUn0_es_varc
#print axioms ReflConsumidor.shapeBin1_es_funcc
#print axioms ReflConsumidor.refl_shapeUn_imp
#print axioms ReflConsumidor.refl_caso_varc
#print axioms ReflConsumidor.refl_caso_funcc
#print axioms ReflConsumidor.refl_lista_nil
#print axioms ReflConsumidor.refl_lista_cons
#print axioms ReflConsumidor.pcc_zero_lt_succ_code
#print axioms ReflConsumidor.pcc_liftc0_var_code
#print axioms ReflConsumidor.pcc_liftc0_func_code
#print axioms ReflConsumidor.pcc_liftsc0_nil_code
#print axioms ReflConsumidor.pcc_liftsc0_cons_code
#print axioms ReflConsumidor.pcc_liftsc_nil_code
#print axioms ReflConsumidor.pcc_liftsc_cons_code
#print axioms ReflConsumidor.pcc_liftc_var_ge_code
#print axioms ReflConsumidor.pcc_liftc_func_code
#print axioms ReflConsumidor.liftcT_termCode
#print axioms ReflConsumidor.varcT_termCode
#print axioms ReflConsumidor.funccT_termCode
#print axioms ReflConsumidor.eqc_eq_eqCodeFn

-- CONTROL: la base sancionada es EXACTAMENTE la que ya carga produccion.
#print axioms ROBINSON_PlusPlus.Meta.EvalNthcPrf.pcc_nthc_zero_code
#print axioms ROBINSON_PlusPlus.Meta.DotConsPrf.pcc_dot_cons
#print axioms ROBINSON_PlusPlus.Meta.Delta0ReflectPrf.pcc_lt_tracked

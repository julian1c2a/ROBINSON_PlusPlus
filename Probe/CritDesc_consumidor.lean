/-
# ESTRATEGIA 3 — LO MINIMO QUE PIDE EL CONSUMIDOR, y el DESCENSO que lo ata.

Fichero AUTOCONTENIDO (`import ROBINSON_PlusPlus.Meta` y nada mas).

    lake env lean Probe/Desc_consumidor.lean

## RESPUESTA A LA PREGUNTA DE LA ESTRATEGIA 3 — **NO HAY AHORRO**

Trabajando hacia atras desde `sondeos/Paso2CasoForall.lean:505`:

* el `s` de `paso2_caso_forall` es el **SUSTITUYENDO**, y en la induccion real
  (`Paso2Ind.PHI`, que es la unica admisible por `prf_strong_induction` porque `hΦ`
  obliga a meter `v`/`s` DENTRO) ese `s` es **literalmente `#0`** (§C1);
* y pedir `targetLift` solo para `#0` **es pedirlo para TODO `s`**: §C1
  `sin_ahorro` lo PRUEBA (de `Prf (targetLift #0)` sale `∀t, Prf (targetLift t)`,
  por `Prf.gen` + `prf_spec`).

⇒ hace falta el UNIVERSAL. Y hace falta **con guarda**: sin guarda el enunciado
   habla de `liftc 0 x` para `x` basura, que la teoria no evalua.

⇒ se construye el DESCENSO (§C6), y en la forma IMPLICATIVA (objeto), que es la
   unica moneda que una induccion OBJETO puede consumir.

## LA SIMPLIFICACION MEDIDA DE ESTE FICHERO

El DESCENSO **no necesita la conjuncion de las dos mitades**: basta la mitad de
LISTAS. La mitad de TERMINOS sale despues, **sin induccion**, porque el unico
disyunto que recurre (`funcc`) pide exactamente la mitad de listas sobre
`nthc X 2̄`. Dentro de la induccion de listas, el caso `funcc` de la CABEZA baja
DOS peldanos de Cantor (`nthc h 2̄ < h < Y`) y vuelve a la MISMA hipotesis de
induccion. ⇒ `PHI` tiene **un solo binder interno** (`∀w`) y **un solo
consecuente**.

## CONTENIDO

* §A — copia LITERAL de `sondeos/ReflectorDesdeConsumidor.lean` §1‑§11.
* §B — copia LITERAL de `sondeos/ClausuraLiftSinWTs.lean` (predicado sin `wTs`)
       y de `sondeos/Paso2CasoForall.lean` §7 (descenso de Cantor).
* §C — NUEVO.
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
open ROBINSON_PlusPlus.Meta.TrackedCorePrf ROBINSON_PlusPlus.Meta.Sigma1CorePrf
open ROBINSON_PlusPlus.Meta.EvalBoundedPrf ROBINSON_PlusPlus.Meta.InAxiomsCodePrf
open ROBINSON_PlusPlus.Meta.Delta0ReflectPrf ROBINSON_PlusPlus.Meta.D3InDotPrf
open ROBINSON_PlusPlus.Meta.CantorMonoPrf ROBINSON_PlusPlus.Meta.NatOrderPrf
open ROBINSON_PlusPlus.Meta.StrongInductionPrf

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

namespace DescCons

/-! # §A · COPIA LITERAL DE `sondeos/ReflectorDesdeConsumidor.lean` §1‑§11 -/

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
    (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prfᵢ.j3 A B C)) (prfH_hyp_self _))
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
      (Prf.incl (Prfᵢ.p1 (targetLift X) (targetLiftsc (nthc X (numeralM 2)))))
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


/-! # §B · COPIA LITERAL de sondeos/ClausuraLiftSinWTs.lean (piezas del predicado) -/

theorem prf_lorL (A B : Formula) : Prf (Formula.impl A (lor A B)) := Prf.incl (Prfᵢ.j1 A B)
theorem prf_lorR (A B : Formula) : Prf (Formula.impl B (lor A B)) := Prf.incl (Prfᵢ.j2 A B)

theorem prf_cdrc_cons (h t : Term) : Prf (cdrc (cons h t) =eq t) := by
  have hax : Prf ax_cdrc := prf_ax (by simp [axioms])
  have hh := prf_spec (prf_spec hax h) t
  simp [substFormula, substTerm, substTerms, cdrc, cons, FOL.substTerm_liftTerm] at hh
  exact hh

theorem prf_congr_lenc {t₁ t₂ : Term} (h : Prf (t₁ =eq t₂)) : Prf (lenc t₁ =eq lenc t₂) := by
  let f : Formula := Formula.eq (lenc (liftTerm 0 t₁)) (lenc (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (lenc t₁) (lenc s) := by
    intro s
    simp only [f, lenc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact prfH_nil_to_prf
    ((hS t₂) ▸ PrfH_leibniz_subst (A := f) (prf_to_prfH h [])
      ((hS t₁) ▸ prf_to_prfH (prf_refl (lenc t₁)) [])) rfl

theorem prf_congr_nthc_lst {w₁ w₂ : Term} (i : Term) (h : Prf (w₁ =eq w₂)) :
    Prf (nthc w₁ i =eq nthc w₂ i) := by
  let f : Formula := Formula.eq (nthc (liftTerm 0 w₁) (liftTerm 0 i)) (nthc (.var 0) (liftTerm 0 i))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (nthc w₁ i) (nthc s i) := by
    intro s
    simp only [f, nthc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact prfH_nil_to_prf
    ((hS w₂) ▸ PrfH_leibniz_subst (A := f) (prf_to_prfH h [])
      ((hS w₁) ▸ prf_to_prfH (prf_refl (nthc w₁ i)) [])) rfl

def consOk (X : Term) : Formula := Formula.eq X (cons (carc X) (cdrc X))
def cOk (X : Term) (F : Formula) : Formula := land (consOk X) F

def wfAll1Body (w : Term) : Formula :=
  Formula.impl (lt (.var 0) (liftTerm 0 (lenc w)))
    (isTermCodeE1 (liftTerm 0 w) (nthc (liftTerm 0 w) (.var 0)))

/-- El testigo es AHORA UNA SOLA LISTA: no hay `p = cons wT wTs`, no hay `carc`/`cdrc`. -/
def wfAll1 (w : Term) : Formula := Formula.forall (wfAll1Body w)

def isTC1 (w c : Term) : Formula := land (wfAll1 w) (In c w)

theorem PrfH_congr_succ {Γ : List Formula} {a b : Term} (h : PrfH Γ (a =eq b)) :
    PrfH Γ (succ a =eq succ b) := by
  let f : Formula := Formula.eq (succ (liftTerm 0 a)) (succ (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (succ a) (succ s) := by
    intro s
    simp only [f, succ, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS b) ▸ PrfH_leibniz_subst (A := f) h ((hS a) ▸ prf_to_prfH (prf_refl (succ a)) Γ)

theorem PrfH_congr_lenc {Γ : List Formula} {a b : Term} (h : PrfH Γ (a =eq b)) :
    PrfH Γ (lenc a =eq lenc b) := by
  let f : Formula := Formula.eq (lenc (liftTerm 0 a)) (lenc (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (lenc a) (lenc s) := by
    intro s
    simp only [f, lenc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS b) ▸ PrfH_leibniz_subst (A := f) h ((hS a) ▸ prf_to_prfH (prf_refl (lenc a)) Γ)

theorem PrfH_congr_liftc {Γ : List Formula} {a b : Term} (v : Term) (h : PrfH Γ (a =eq b)) :
    PrfH Γ (liftc v a =eq liftc v b) := by
  let f : Formula := Formula.eq (liftc (liftTerm 0 v) (liftTerm 0 a)) (liftc (liftTerm 0 v) (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (liftc v a) (liftc v s) := by
    intro s
    simp only [f, liftc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS b) ▸ PrfH_leibniz_subst (A := f) h ((hS a) ▸ prf_to_prfH (prf_refl (liftc v a)) Γ)

theorem PrfH_congr_nthc_lst {Γ : List Formula} {a b : Term} (i : Term) (h : PrfH Γ (a =eq b)) :
    PrfH Γ (nthc a i =eq nthc b i) := by
  let f : Formula := Formula.eq (nthc (liftTerm 0 a) (liftTerm 0 i)) (nthc (.var 0) (liftTerm 0 i))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (nthc a i) (nthc s i) := by
    intro s
    simp only [f, nthc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS b) ▸ PrfH_leibniz_subst (A := f) h ((hS a) ▸ prf_to_prfH (prf_refl (nthc a i)) Γ)

theorem PrfH_congr_nthc_idx {Γ : List Formula} {i j : Term} (L : Term) (h : PrfH Γ (i =eq j)) :
    PrfH Γ (nthc L i =eq nthc L j) := by
  let f : Formula := Formula.eq (nthc (liftTerm 0 L) (liftTerm 0 i)) (nthc (liftTerm 0 L) (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (nthc L i) (nthc L s) := by
    intro s
    simp only [f, nthc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS j) ▸ PrfH_leibniz_subst (A := f) h ((hS i) ▸ prf_to_prfH (prf_refl (nthc L i)) Γ)

theorem PrfH_congr_In_left {Γ : List Formula} {u v w : Term} (h : PrfH Γ (u =eq v))
    (hin : PrfH Γ (In u w)) : PrfH Γ (In v w) := by
  have hS : ∀ s : Term, substFormula 0 s (In (.var 0) (liftTerm 0 w)) = In s w := by
    intro s
    simp only [In, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS v) ▸ PrfH_leibniz_subst (A := In (.var 0) (liftTerm 0 w)) h ((hS u) ▸ hin)

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

/-- Leibniz en el 2º argumento de `argsIn` (la lista de argumentos). -/
theorem PrfH_congr_argsIn {Γ : List Formula} {wT Y₁ Y₂ : Term} (h : PrfH Γ (Y₁ =eq Y₂))
    (ha : PrfH Γ (argsIn wT Y₁)) : PrfH Γ (argsIn wT Y₂) := by
  have hS : ∀ s : Term, substFormula 0 s (argsIn (liftTerm 0 wT) (.var 0)) = argsIn wT s := by
    intro s
    simp only [substF_argsIn, substTerm, FOL.substTerm_liftTerm, if_true]
  exact (hS Y₂) ▸ PrfH_leibniz_subst (A := argsIn (liftTerm 0 wT) (.var 0)) h ((hS Y₁) ▸ ha)

/-- Leibniz en el 2º argumento de `isTermCodeE1` (el nodo). **Una** Leibniz cubre las
    5 ocurrencias del hueco. -/
theorem PrfH_congr_isTermCodeE1 {Γ : List Formula} {wT X₁ X₂ : Term} (h : PrfH Γ (X₁ =eq X₂))
    (ha : PrfH Γ (isTermCodeE1 wT X₁)) : PrfH Γ (isTermCodeE1 wT X₂) := by
  have hS : ∀ s : Term,
      substFormula 0 s (isTermCodeE1 (liftTerm 0 wT) (.var 0)) = isTermCodeE1 wT s := by
    intro s
    simp only [substF_isTermCodeE1, substTerm, FOL.substTerm_liftTerm, if_true]
  exact (hS X₂) ▸ PrfH_leibniz_subst (A := isTermCodeE1 (liftTerm 0 wT) (.var 0)) h ((hS X₁) ▸ ha)

/-- Instanciacion de `argsIn` en un indice CUALQUIERA (el testigo puede ser ABIERTO). -/
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

/-! ### NO VACUIDAD: el testigo COMPUTABLE — copia de ClausuraLiftSinWTs §5 -/

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

/-! ### El DESCENSO de CANTOR — copia de sondeos/Paso2CasoForall.lean §7 -/

/-- **DESCENSO unario**: de la forma ecuacional sale `nthc X 1 < X`. -/
theorem descenso_un (X : Term) (k : Nat) : Prf (shapeUn X k ⇒ lt (nthc X (numeralM 1)) X) := by
  refine prf_deduction ?_
  have h1 : Prf (lt (nthc X (numeralM 1)) (cons (nthc X (numeralM 1)) nil)) :=
    prf_cantor_mono_left _ _
  have h2 : Prf (lt (cons (nthc X (numeralM 1)) nil)
      (cons (numeralM k) (cons (nthc X (numeralM 1)) nil))) := prf_cantor_mono_right _ _
  have h3 : Prf (lt (nthc X (numeralM 1)) (cons (numeralM k) (cons (nthc X (numeralM 1)) nil))) :=
    prf_mp (prf_mp (prf_lt_trans _ _ _) h1) h2
  exact ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2
    (PrfH_eq_symm (prfH_hyp_self (shapeUn X k))) (prf_to_prfH h3 _)

/-- **DESCENSO binario, 1er hijo**. -/
theorem descenso_bin1 (X : Term) (k : Nat) : Prf (shapeBin X k ⇒ lt (nthc X (numeralM 1)) X) := by
  refine prf_deduction ?_
  have h1 : Prf (lt (nthc X (numeralM 1))
      (cons (nthc X (numeralM 1)) (cons (nthc X (numeralM 2)) nil))) := prf_cantor_mono_left _ _
  have h2 : Prf (lt (cons (nthc X (numeralM 1)) (cons (nthc X (numeralM 2)) nil))
      (cons (numeralM k) (cons (nthc X (numeralM 1)) (cons (nthc X (numeralM 2)) nil)))) :=
    prf_cantor_mono_right _ _
  have h3 : Prf (lt (nthc X (numeralM 1))
      (cons (numeralM k) (cons (nthc X (numeralM 1)) (cons (nthc X (numeralM 2)) nil)))) :=
    prf_mp (prf_mp (prf_lt_trans _ _ _) h1) h2
  exact ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2
    (PrfH_eq_symm (prfH_hyp_self (shapeBin X k))) (prf_to_prfH h3 _)

/-- **DESCENSO binario, 2o hijo** (dos transitividades). -/
theorem descenso_bin2 (X : Term) (k : Nat) : Prf (shapeBin X k ⇒ lt (nthc X (numeralM 2)) X) := by
  refine prf_deduction ?_
  have h1 : Prf (lt (nthc X (numeralM 2)) (cons (nthc X (numeralM 2)) nil)) :=
    prf_cantor_mono_left _ _
  have h2 : Prf (lt (cons (nthc X (numeralM 2)) nil)
      (cons (nthc X (numeralM 1)) (cons (nthc X (numeralM 2)) nil))) := prf_cantor_mono_right _ _
  have h3 : Prf (lt (cons (nthc X (numeralM 1)) (cons (nthc X (numeralM 2)) nil))
      (cons (numeralM k) (cons (nthc X (numeralM 1)) (cons (nthc X (numeralM 2)) nil)))) :=
    prf_cantor_mono_right _ _
  have h4 : Prf (lt (nthc X (numeralM 2))
      (cons (nthc X (numeralM 1)) (cons (nthc X (numeralM 2)) nil))) :=
    prf_mp (prf_mp (prf_lt_trans _ _ _) h1) h2
  have h5 : Prf (lt (nthc X (numeralM 2))
      (cons (numeralM k) (cons (nthc X (numeralM 1)) (cons (nthc X (numeralM 2)) nil)))) :=
    prf_mp (prf_mp (prf_lt_trans _ _ _) h4) h3
  exact ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2
    (PrfH_eq_symm (prfH_hyp_self (shapeBin X k))) (prf_to_prfH h5 _)

/-! # §C · NUEVO

    §C1 la MEDIDA (respuesta a la estrategia 3) · §C2‑§C5 la fontaneria que falta ·
    §C6 el DESCENSO. -/

/-! ## §C1 · LA MEDIDA: el `s` del consumidor es `#0`, y eso NO es ningun ahorro -/

/-- Constructor de codigo del `substfc` DOTADO (copia de `Paso2.substfcT`). Es una
    DEFINICION: ninguna ecuacion suya se postula. -/
def substfcT (v s f : Term) : Term :=
  funcc (strCode "substfc") (cons v (cons s (cons f nil)))

/-- El codigo de la ecuacion interna del PASO 2 (copia de `Paso2.evalSubstfcCode`). -/
def evalSubstfcCode (v s f : Term) : Term :=
  eqCodeFn (substfcT (tcFn v) (tcFn s) (tcFn f)) (tcFn (substfc v s f))

theorem liftTerm_evalSubstfcCode (k : Nat) (v s f : Term) :
    liftTerm k (evalSubstfcCode v s f)
      = evalSubstfcCode (liftTerm k v) (liftTerm k s) (liftTerm k f) := by
  simp only [evalSubstfcCode, eqCodeFn, substfcT, funcc, tcFn, substfc, cons, nil, zero, succ,
    liftTerm, liftTerms, liftTerm_numeral, liftTerm_strCode]

/-- El predicado de la induccion del PASO 2 (copia de `Paso2Ind.PHI`): `v` y `s` van
    cuantificados DENTRO porque `prf_strong_induction` exige `liftFormula 1 Φ = Φ`. -/
def PHI2 : Formula :=
  Formula.forall (Formula.forall (provFromCode (evalSubstfcCode (.var 1) (.var 0) (.var 2))))

theorem PHI2_lift : liftFormula 1 PHI2 = PHI2 := by
  simp only [PHI2, liftFormula, liftFormula_provFromCode_open, liftTerm_evalSubstfcCode,
    liftTerm, Nat.reduceLT, Nat.reduceAdd, reduceIte, if_true]

/-- **EL `s` DEL CONSUMIDOR ES `#0`**, por `rfl`: en el cuerpo de `PHI2` la ranura del
    SUSTITUYENDO (2ª de `evalSubstfcCode`) es literalmente `Term.var 0`. -/
theorem el_s_del_consumidor_es_var0 :
    PHI2 = Formula.forall (Formula.forall
      (provFromCode (evalSubstfcCode (.var 1) (Term.var 0) (.var 2)))) := rfl

/-- **NO HAY AHORRO.** Pedir el `hLift` de `paso2_caso_forall` SOLO para el `s` que
    aparece alli (que es `#0`) **es pedirlo para TODO `s`**: `Prf.gen` + `prf_spec`.

    ⇒ la estrategia 3 se responde en NEGATIVO: hace falta el universal. -/
theorem sin_ahorro (h : Prf (targetLift (Term.var 0))) : ∀ t : Term, Prf (targetLift t) := by
  intro t
  have hg : Prf (Formula.forall (provFromCode (eqc (liftcT (termCode zero) (tcFn (.var 0)))
      (tcFn (liftc zero (.var 0)))))) := Prf.gen _ h
  have hs := prf_spec hg t
  rwa [substF_targetLift_hole] at hs

/-! ## §C2 · MONOTONIA DEL CONTEXTO EN `PrfH` (no estaba) -/

theorem PrfH_mono : ∀ {Γ : List Formula} {ψ : Formula}, PrfH Γ ψ →
    ∀ Δ : List Formula, (∀ φ, List.Mem φ Γ → List.Mem φ Δ) → PrfH Δ ψ := by
  intro Γ ψ h
  induction h with
  | hyp Γ' φ hm => intro Δ hsub; exact PrfH.hyp Δ φ (hsub φ hm)
  | incl0 Γ' φ h0 => intro Δ _; exact PrfH.incl0 Δ φ h0
  | p3 Γ' A => intro Δ _; exact PrfH.p3 Δ A
  | ind Γ' A => intro Δ _; exact PrfH.ind Δ A
  | qconf Γ' P C => intro Δ _; exact PrfH.qconf Δ P C
  | listInd Γ' A => intro Δ _; exact PrfH.listInd Δ A
  | mp Γ' A B hAB hA ihAB ihA => intro Δ hsub; exact PrfH.mp Δ A B (ihAB Δ hsub) (ihA Δ hsub)
  | gen Γ' A hdd ih =>
      intro Δ hsub
      refine PrfH.gen Δ A (ih (Δ.map (liftFormula 0)) ?_)
      intro φ hm
      have hm' : φ ∈ Γ'.map (liftFormula 0) := hm
      rcases List.mem_map.mp hm' with ⟨ψ0, hψ0, rfl⟩
      exact List.mem_map.mpr ⟨ψ0, hsub ψ0 hψ0, rfl⟩

/-- Debilitamiento por una hipotesis. -/
theorem PrfH_w1 {Γ : List Formula} {A ψ : Formula} (h : PrfH Γ ψ) : PrfH (A :: Γ) ψ :=
  PrfH_mono h _ (fun _ hm => List.Mem.tail _ hm)

/-! ## §C3 · LA ESTRUCTURA QUE `argsIn` NO DA: `Y ≐ nil ∨ Y ≐ cons (carc Y) (cdrc Y)`

    `argsIn` es POSICIONAL (habla de `lenc`/`nthc`) y **no** fuerza que la lista de
    argumentos sea una cadena `cons` (agujero (b) de `ClausuraLiftSinWTs` §8). La
    estructura se recupera **sin axiomas nuevos**: por la regla `Prf.listInd` del calculo,
    cuyo paso NO usa siquiera la hipotesis de induccion. -/

theorem prf_weak_imp {A B : Formula} (h : Prf B) : Prf (Formula.impl A B) :=
  prf_mp (Prf.incl (Prfᵢ.p1 B A)) h

/-- `cons a b ≐ cons (carc (cons a b)) (cdrc (cons a b))`. -/
theorem prf_cons_eq_carcdr (a b : Term) :
    Prf (Formula.eq (cons a b) (cons (carc (cons a b)) (cdrc (cons a b)))) :=
  prf_eq_symm (prf_eq_trans (prf_congr_cons_head (prf_carc_cons a b))
    (prf_congr_cons_tail (prf_cdrc_cons a b)))

def NILCONS : Formula :=
  lor (Formula.eq (.var 0) nil) (Formula.eq (.var 0) (cons (carc (.var 0)) (cdrc (.var 0))))

theorem prf_nil_or_cons_all : Prf (Formula.forall NILCONS) := by
  refine prf_list_induction NILCONS ?base ?step
  · have e : substFormula 0 nil NILCONS
        = lor (Formula.eq nil nil) (Formula.eq nil (cons (carc nil) (cdrc nil))) := by
      simp only [NILCONS, lor, nil, zero, cons, carc, cdrc, substFormula, substTerm, substTerms,
        reduceIte, if_true]
    rw [e]
    exact prf_orL (prf_refl nil)
  · refine Prf.gen _ (Prf.gen _ ?_)
    have e1 : liftFormula 1 NILCONS = NILCONS := by
      simp only [NILCONS, lor, nil, zero, cons, carc, cdrc, liftFormula, liftTerm, liftTerms,
        Nat.zero_lt_succ, reduceIte, if_true]
    rw [e1]
    have e2 : substFormula 0 (cons (.var 1) (.var 0)) (liftFormula 2 NILCONS)
        = lor (Formula.eq (cons (.var 1) (.var 0)) nil)
              (Formula.eq (cons (.var 1) (.var 0))
                (cons (carc (cons (.var 1) (.var 0))) (cdrc (cons (.var 1) (.var 0))))) := by
      simp only [NILCONS, lor, nil, zero, cons, carc, cdrc, liftFormula, liftTerm, liftTerms,
        substFormula, substTerm, substTerms, Nat.reduceAdd, Nat.reduceLT, Nat.zero_lt_succ,
        reduceIte, if_true]
    rw [e2]
    exact prf_weak_imp (prf_orR (prf_cons_eq_carcdr (.var 1) (.var 0)))

/-- **LA DESCOMPOSICION, para `Y` ARBITRARIO.** Cero axiomas: sale de `Prf.listInd`. -/
theorem prf_nil_or_cons (Y : Term) :
    Prf (lor (Formula.eq Y nil) (Formula.eq Y (cons (carc Y) (cdrc Y)))) := by
  have h := prf_spec prf_nil_or_cons_all Y
  simpa only [NILCONS, lor, nil, zero, cons, carc, cdrc, substFormula, substTerm, substTerms,
    reduceIte, if_true] using h

/-! ## §C4 · `isTC1 w c ⇒ isTermCodeE1 w c` (el testigo se lee por POSICION) -/

theorem liftF_isTC1 (k : Nat) (w c : Term) :
    liftFormula k (isTC1 w c) = isTC1 (liftTerm k w) (liftTerm k c) := by
  simp only [isTC1, land, liftFormula, liftF_wfAll1, In, liftTerm, liftTerms]

theorem prf_isTC1_isTermCodeE1 (w c : Term) :
    Prf (Formula.impl (isTC1 w c) (isTermCodeE1 w c)) := by
  refine prf_deduction ?_
  have hh : PrfH [isTC1 w c] (isTC1 w c) := prfH_hyp_self _
  have hin : PrfH [isTC1 w c] (In c w) := PrfH_and_elim_right hh
  have hbd : PrfH [isTC1 w c] (boundedIn c w) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_boundedIn_of_In c w) _) hin
  refine PrfH_ex_elim hbd ?_
  rw [liftF_isTermCodeE1]
  have hctx : [isTC1 w c].map (liftFormula 0) = [isTC1 (liftTerm 0 w) (liftTerm 0 c)] := by
    simp only [List.map_cons, List.map_nil, liftF_isTC1]
  rw [hctx]
  have hlenc : liftTerm 0 (lenc w) = lenc (liftTerm 0 w) := by
    simp only [lenc, liftTerm, liftTerms]
  rw [hlenc]
  have hcj : PrfH [land (lt (.var 0) (lenc (liftTerm 0 w)))
        (Formula.eq (nthc (liftTerm 0 w) (.var 0)) (liftTerm 0 c)),
      isTC1 (liftTerm 0 w) (liftTerm 0 c)]
      (land (lt (.var 0) (lenc (liftTerm 0 w)))
        (Formula.eq (nthc (liftTerm 0 w) (.var 0)) (liftTerm 0 c))) :=
    PrfH.hyp _ _ (List.Mem.head _)
  have hitc : PrfH [land (lt (.var 0) (lenc (liftTerm 0 w)))
        (Formula.eq (nthc (liftTerm 0 w) (.var 0)) (liftTerm 0 c)),
      isTC1 (liftTerm 0 w) (liftTerm 0 c)]
      (land (wfAll1 (liftTerm 0 w)) (In (liftTerm 0 c) (liftTerm 0 w))) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  exact PrfH_congr_isTermCodeE1 (PrfH_and_elim_right hcj)
    (PrfH.mp _ _ _ (PrfH_inst_wfAll1 (liftTerm 0 w) (.var 0) (PrfH_and_elim_left hitc))
      (PrfH_and_elim_left hcj))

/-! ## §C5 · `argsIn` sobre un `cons`: CABEZA y COLA -/

theorem prf_argsIn_head (w hd tl : Term) :
    Prf (Formula.impl (argsIn w (cons hd tl)) (In hd w)) := by
  refine prf_deduction ?_
  have ha : PrfH [argsIn w (cons hd tl)] (argsIn w (cons hd tl)) := prfH_hyp_self _
  have hlt : PrfH [argsIn w (cons hd tl)] (lt zero (lenc (cons hd tl))) :=
    ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2
      (prf_to_prfH (prf_eq_symm (prf_lenc_cons hd tl)) _)
      (prf_to_prfH (prf_zero_lt_succ (lenc tl)) _)
  have hin := PrfH.mp _ _ _ (PrfH_inst_argsIn w (cons hd tl) zero ha) hlt
  exact PrfH_congr_In_left (prf_to_prfH (prf_nthc_zero hd tl) _) hin

theorem prf_argsIn_tail_body (W H T i : Term) :
    Prf (Formula.impl (argsIn W (cons H T))
      (Formula.impl (lt i (lenc T)) (In (nthc T i) W))) := by
  refine prf_deduction (deduction_aux ?_ (lt i (lenc T)) [argsIn W (cons H T)] rfl)
  have hlt : PrfH [lt i (lenc T), argsIn W (cons H T)] (lt i (lenc T)) :=
    PrfH.hyp _ _ (List.Mem.head _)
  have ha : PrfH [lt i (lenc T), argsIn W (cons H T)] (argsIn W (cons H T)) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hlt2 : PrfH [lt i (lenc T), argsIn W (cons H T)] (lt (succ i) (succ (lenc T))) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_succ_lt_succ_of_lt i (lenc T)) _) hlt
  have hlt3 : PrfH [lt i (lenc T), argsIn W (cons H T)] (lt (succ i) (lenc (cons H T))) :=
    ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2
      (prf_to_prfH (prf_eq_symm (prf_lenc_cons H T)) _) hlt2
  have hin := PrfH.mp _ _ _ (PrfH_inst_argsIn W (cons H T) (succ i) ha) hlt3
  exact PrfH_congr_In_left (prf_to_prfH (prf_nthc_succ H T i) _) hin

theorem prf_argsIn_tail (w hd tl : Term) :
    Prf (Formula.impl (argsIn w (cons hd tl)) (argsIn w tl)) := by
  refine prf_mp (Prf.qconf (argsIn w (cons hd tl)) (argsInBody w tl)) (Prf.gen _ ?_)
  rw [liftF_argsIn]
  show Prf (Formula.impl (argsIn (liftTerm 0 w) (liftTerm 0 (cons hd tl)))
    (Formula.impl (lt (.var 0) (liftTerm 0 (lenc tl)))
      (In (nthc (liftTerm 0 tl) (.var 0)) (liftTerm 0 w))))
  have e1 : liftTerm 0 (cons hd tl) = cons (liftTerm 0 hd) (liftTerm 0 tl) := by
    simp only [cons, liftTerm, liftTerms]
  have e2 : liftTerm 0 (lenc tl) = lenc (liftTerm 0 tl) := by
    simp only [lenc, liftTerm, liftTerms]
  rw [e1, e2]
  exact prf_argsIn_tail_body (liftTerm 0 w) (liftTerm 0 hd) (liftTerm 0 tl) (.var 0)

/-! ## §C6 · EL DESCENSO

    Una sola induccion FUERTE, sobre el VALOR del codigo, con **un solo** binder interno
    (`∀w`) y **un solo** consecuente (la mitad de LISTAS). La mitad de TERMINOS sale
    despues **sin induccion**. -/

/-! ### §C6.a · `targetLiftsc` bajo `lift`/`subst` y su Leibniz -/

mutual
theorem liftTerm_termCode (k : Nat) : ∀ t : Term, liftTerm k (termCode t) = termCode t
  | .var _ => by simp only [termCode, cons, nil, zero, liftTerm, liftTerms, liftTerm_numeral]
  | .func s ts => by
      simp only [termCode, cons, nil, zero, liftTerm, liftTerms, liftTerm_numeral,
        liftTerm_strCode, liftTerm_termsCode k ts]
theorem liftTerm_termsCode (k : Nat) : ∀ ts : List Term, liftTerm k (termsCode ts) = termsCode ts
  | []      => rfl
  | t :: ts => by
      simp only [termsCode, cons, liftTerm, liftTerms, liftTerm_termCode k t,
        liftTerm_termsCode k ts]
end

theorem liftF_targetLiftsc (k : Nat) (b : Term) :
    liftFormula k (targetLiftsc b) = targetLiftsc (liftTerm k b) := by
  simp only [targetLiftsc, liftFormula_provFromCode_open, eqc, eqCodeFn, atom2CodeFn, liftscT,
    funcc, tcFn, liftsc, cons, nil, zero, succ, liftTerm, liftTerms, liftTerm_numeral,
    liftTerm_strCode, liftTerm_termCode]

theorem substF_targetLiftsc (v : Nat) (s b : Term) :
    substFormula v s (targetLiftsc b) = targetLiftsc (substTerm v s b) := by
  simp only [targetLiftsc, substFormula_provFromCode_open, eqc, eqCodeFn, atom2CodeFn, liftscT,
    funcc, tcFn, liftsc, cons, nil, zero, succ, substTerm, substTerms, substTerm_numeral,
    substTerm_strCode, substTerm_termCode]

theorem substF_targetLiftsc_hole (t : Term) :
    substFormula 0 t (targetLiftsc (.var 0)) = targetLiftsc t := by
  simp only [substF_targetLiftsc, substTerm, reduceIte, if_true]

theorem PrfH_congr_targetLiftsc {Γ : List Formula} {a b : Term} (h : PrfH Γ (a =eq b))
    (ha : PrfH Γ (targetLiftsc a)) : PrfH Γ (targetLiftsc b) :=
  (substF_targetLiftsc_hole b) ▸
    PrfH_leibniz_subst (A := targetLiftsc (.var 0)) h ((substF_targetLiftsc_hole a) ▸ ha)

theorem substF_wfAll1 (v : Nat) (s w : Term) :
    substFormula v s (wfAll1 w) = wfAll1 (substTerm v s w) := by
  have hz : (0 = v + 1) = False := eq_false (by omega)
  have hz2 : (0 > v + 1) = False := eq_false (by omega)
  simp only [wfAll1, wfAll1Body, substFormula, substF_isTermCodeE1, lt, lenc, nthc,
    substTerm, substTerms, liftTerm, liftTerms, hz, hz2, if_false, Nat.zero_lt_succ,
    reduceIte, if_true, FOL.substTerm_lift_comm_zero]

/-! ### §C6.b · El predicado de la induccion y la HI -/

def DBODY : Formula :=
  Formula.impl (land (wfAll1 (.var 0)) (argsIn (.var 0) (.var 1))) (targetLiftsc (.var 1))

def DPHI : Formula := Formula.forall DBODY

/-- El gate de `prf_strong_induction`: `w` cuantificado DENTRO ⇒ `Φ` solo tiene libre el
    codigo sobre el que se induce. -/
theorem DPHI_lift : liftFormula 1 DPHI = DPHI := by
  simp only [DPHI, DBODY, land, liftFormula, liftF_wfAll1, liftF_argsIn, liftF_targetLiftsc,
    liftTerm, Nat.reduceAdd, Nat.reduceLT, Nat.zero_lt_succ, reduceIte, if_true]

theorem DPHI_at (t : Term) :
    substFormula 0 t DPHI
      = Formula.forall (Formula.impl
          (land (wfAll1 (.var 0)) (argsIn (.var 0) (liftTerm 0 t)))
          (targetLiftsc (liftTerm 0 t))) := by
  simp only [DPHI, DBODY, land, substFormula, substF_wfAll1, substF_argsIn, substF_targetLiftsc,
    substTerm, Nat.reduceAdd, Nat.reduceEqDiff, Nat.reduceGT, Nat.reduceSub, reduceIte,
    if_true, if_false]

theorem psi_lift_form :
    liftFormula 0 (PSI DPHI) = Formula.forall (Formula.impl (lt (.var 0) (.var 2)) DPHI) := by
  simp only [PSI, liftFormula, lt, liftTerm, liftTerms, Nat.reduceAdd, Nat.reduceLT,
    Nat.zero_lt_succ, reduceIte, if_true, DPHI_lift]

/-- **LA HIPOTESIS DE INDUCCION, LISTA PARA USAR.** En el contexto del paso, `#0` es el
    testigo `w` y `#1` es el codigo `X`; de `m < X` y del par (`wfAll1 w`, `argsIn w m`)
    sale `targetLiftsc m`. -/
theorem PrfH_IH {Γ : List Formula} (m : Term)
    (hpsi : PrfH Γ (liftFormula 0 (PSI DPHI)))
    (hlt : PrfH Γ (lt m (.var 1)))
    (hwf : PrfH Γ (wfAll1 (.var 0)))
    (hargs : PrfH Γ (argsIn (.var 0) m)) :
    PrfH Γ (targetLiftsc m) := by
  rw [psi_lift_form] at hpsi
  have h1 := PrfH_spec hpsi m
  have e1 : substFormula 0 m (Formula.impl (lt (.var 0) (.var 2)) DPHI)
      = Formula.impl (lt m (.var 1)) (substFormula 0 m DPHI) := by
    simp only [substFormula, lt, substTerm, substTerms, Nat.reduceEqDiff, Nat.reduceGT,
      Nat.reduceSub, reduceIte, if_true, if_false]
  rw [e1, DPHI_at] at h1
  have h2 := PrfH_spec (PrfH.mp _ _ _ h1 hlt) (.var 0)
  have e2 : substFormula 0 (.var 0) (Formula.impl
        (land (wfAll1 (.var 0)) (argsIn (.var 0) (liftTerm 0 m)))
        (targetLiftsc (liftTerm 0 m)))
      = Formula.impl (land (wfAll1 (.var 0)) (argsIn (.var 0) m)) (targetLiftsc m) := by
    simp only [substFormula, land, substF_wfAll1, substF_argsIn, substF_targetLiftsc,
      substTerm, FOL.substTerm_liftTerm, reduceIte, if_true]
  rw [e2] at h2
  exact PrfH.mp _ _ _ h2 (PrfH_and_intro hwf hargs)

/-! ### §C6.c · EL PASO, con el contexto ABSTRACTO -/

/-- La CABEZA de la lista: de `In hd w` (+ testigo) sale `targetLift hd`. El disyunto
    `funcc` baja DOS peldanos de Cantor (`nthc hd 2̄ < hd < X`) y vuelve a la MISMA HI. -/
theorem head_targetLift {Γ : List Formula} (hd : Term)
    (hpsi : PrfH Γ (liftFormula 0 (PSI DPHI)))
    (hwf : PrfH Γ (wfAll1 (.var 0)))
    (hlth : PrfH Γ (lt hd (.var 1)))
    (hIn : PrfH Γ (In hd (.var 0))) :
    PrfH Γ (targetLift hd) := by
  have hE1 : PrfH Γ (lor (shapeUn hd 0)
      (land (shapeBin hd 1) (argsIn (.var 0) (nthc hd (numeralM 2))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_isTC1_isTermCodeE1 (.var 0) hd) _)
      (PrfH_and_intro hwf hIn)
  refine PrfH_or_elim hE1 ?_ ?_
  · exact PrfH.mp _ _ _ (prf_to_prfH (refl_shapeUn_imp hd) _)
      (PrfH.hyp _ _ (List.Mem.head _))
  · have hcj : PrfH (land (shapeBin hd 1) (argsIn (.var 0) (nthc hd (numeralM 2))) :: Γ)
        (land (shapeBin hd 1) (argsIn (.var 0) (nthc hd (numeralM 2)))) :=
      PrfH.hyp _ _ (List.Mem.head _)
    have hsb := PrfH_and_elim_left hcj
    have hab := PrfH_and_elim_right hcj
    have hltb := PrfH.mp _ _ _ (prf_to_prfH (descenso_bin2 hd 1) _) hsb
    have hltbX := PrfH.mp _ _ _ (PrfH.mp _ _ _
      (prf_to_prfH (prf_lt_trans (nthc hd (numeralM 2)) hd (.var 1)) _) hltb)
      (PrfH_w1 (A := land (shapeBin hd 1) (argsIn (.var 0) (nthc hd (numeralM 2)))) hlth)
    have hTLb := PrfH_IH (nthc hd (numeralM 2))
      (PrfH_w1 (A := land (shapeBin hd 1) (argsIn (.var 0) (nthc hd (numeralM 2)))) hpsi)
      hltbX
      (PrfH_w1 (A := land (shapeBin hd 1) (argsIn (.var 0) (nthc hd (numeralM 2)))) hwf) hab
    exact PrfH.mp _ _ _ (prf_to_prfH (refl_shapeBin_imp hd) _) (PrfH_and_intro hsb hTLb)

/-- El cuerpo del paso, con `Γ` ABSTRACTO: `#0` es el testigo, `#1` el codigo. -/
theorem step_body {Γ : List Formula}
    (hpsi : PrfH Γ (liftFormula 0 (PSI DPHI)))
    (hwf : PrfH Γ (wfAll1 (.var 0)))
    (hargs : PrfH Γ (argsIn (.var 0) (.var 1))) :
    PrfH Γ (targetLiftsc (.var 1)) := by
  have hdec : PrfH Γ (lor (Formula.eq (.var 1) nil)
      (Formula.eq (.var 1) (cons (carc (.var 1)) (cdrc (.var 1))))) :=
    prf_to_prfH (prf_nil_or_cons (.var 1)) Γ
  refine PrfH_or_elim hdec ?_ ?_
  · exact PrfH_congr_targetLiftsc (PrfH_eq_symm (PrfH.hyp _ _ (List.Mem.head _)))
      (prf_to_prfH refl_lista_nil _)
  · have hx : PrfH (Formula.eq (.var 1) (cons (carc (.var 1)) (cdrc (.var 1))) :: Γ)
        (Formula.eq (.var 1) (cons (carc (.var 1)) (cdrc (.var 1)))) :=
      PrfH.hyp _ _ (List.Mem.head _)
    have hpsi' : PrfH (Formula.eq (.var 1) (cons (carc (.var 1)) (cdrc (.var 1))) :: Γ)
        (liftFormula 0 (PSI DPHI)) := PrfH_w1 hpsi
    have hwf' : PrfH (Formula.eq (.var 1) (cons (carc (.var 1)) (cdrc (.var 1))) :: Γ)
        (wfAll1 (.var 0)) := PrfH_w1 hwf
    have hargs' : PrfH (Formula.eq (.var 1) (cons (carc (.var 1)) (cdrc (.var 1))) :: Γ)
        (argsIn (.var 0) (.var 1)) := PrfH_w1 hargs
    have hargsC := PrfH_congr_argsIn hx hargs'
    have hInh := PrfH.mp _ _ _
      (prf_to_prfH (prf_argsIn_head (.var 0) (carc (.var 1)) (cdrc (.var 1))) _) hargsC
    have hargsT := PrfH.mp _ _ _
      (prf_to_prfH (prf_argsIn_tail (.var 0) (carc (.var 1)) (cdrc (.var 1))) _) hargsC
    have hlth := ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2 (PrfH_eq_symm hx)
      (prf_to_prfH (prf_cantor_mono_left (carc (.var 1)) (cdrc (.var 1))) _)
    have hltt := ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2 (PrfH_eq_symm hx)
      (prf_to_prfH (prf_cantor_mono_right (carc (.var 1)) (cdrc (.var 1))) _)
    have hTLt := PrfH_IH (cdrc (.var 1)) hpsi' hltt hwf' hargsT
    have hTLh := head_targetLift (carc (.var 1)) hpsi' hwf' hlth hInh
    have hcons := PrfH.mp _ _ _
      (prf_to_prfH (refl_lista_cons_imp (carc (.var 1)) (cdrc (.var 1))) _)
      (PrfH_and_intro hTLh hTLt)
    exact PrfH_congr_targetLiftsc (PrfH_eq_symm hx) hcons

theorem DPHI_step : Prf (Formula.forall (Formula.impl (PSI DPHI) DPHI)) := by
  refine Prf.gen _ (prf_deduction ?_)
  refine PrfH.gen _ DBODY ?_
  simp only [List.map_cons, List.map_nil]
  refine deduction_aux ?_ (land (wfAll1 (.var 0)) (argsIn (.var 0) (.var 1)))
    [liftFormula 0 (PSI DPHI)] rfl
  have hpsi : PrfH [land (wfAll1 (.var 0)) (argsIn (.var 0) (.var 1)),
      liftFormula 0 (PSI DPHI)] (liftFormula 0 (PSI DPHI)) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hcj : PrfH [land (wfAll1 (.var 0)) (argsIn (.var 0) (.var 1)),
      liftFormula 0 (PSI DPHI)] (land (wfAll1 (.var 0)) (argsIn (.var 0) (.var 1))) :=
    PrfH.hyp _ _ (List.Mem.head _)
  exact step_body hpsi (PrfH_and_elim_left hcj) (PrfH_and_elim_right hcj)

/-! ### §C6.d · EL DESCENSO, las dos mitades -/

/-- **DESCENSO, mitad de LISTAS**: con testigo y `argsIn`, la lista de argumentos entera
    tiene su ecuacion de `liftsc` DOTADA. `w`, `Y` **ABSTRACTOS**. -/
theorem desc_lista (w Y : Term) :
    Prf (Formula.impl (land (wfAll1 w) (argsIn w Y)) (targetLiftsc Y)) := by
  have h := prf_strong_induction DPHI DPHI_lift DPHI_step Y
  rw [DPHI_at] at h
  have h2 := prf_spec h w
  simpa only [substFormula, land, substF_wfAll1, substF_argsIn, substF_targetLiftsc,
    substTerm, FOL.substTerm_liftTerm, reduceIte, if_true] using h2

/-- **EL DESCENSO** — la obligacion abierta del frente, cerrada. `w`, `c` **ABSTRACTOS**,
    forma IMPLICATIVA (la moneda que consume una induccion OBJETO). -/
theorem descenso (w c : Term) : Prf (Formula.impl (isTC1 w c) (targetLift c)) := by
  refine prf_deduction ?_
  have hh : PrfH [isTC1 w c] (land (wfAll1 w) (In c w)) := prfH_hyp_self _
  have hwf : PrfH [isTC1 w c] (wfAll1 w) := PrfH_and_elim_left hh
  have hE1 : PrfH [isTC1 w c] (lor (shapeUn c 0)
      (land (shapeBin c 1) (argsIn w (nthc c (numeralM 2))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_isTC1_isTermCodeE1 w c) _) hh
  refine PrfH_or_elim hE1 ?_ ?_
  · exact PrfH.mp _ _ _ (prf_to_prfH (refl_shapeUn_imp c) _) (PrfH.hyp _ _ (List.Mem.head _))
  · have hcj : PrfH (land (shapeBin c 1) (argsIn w (nthc c (numeralM 2))) :: [isTC1 w c])
        (land (shapeBin c 1) (argsIn w (nthc c (numeralM 2)))) := PrfH.hyp _ _ (List.Mem.head _)
    have hsb := PrfH_and_elim_left hcj
    have hab := PrfH_and_elim_right hcj
    have hTLb := PrfH.mp _ _ _
      (prf_to_prfH (desc_lista w (nthc c (numeralM 2))) _)
      (PrfH_and_intro
        (PrfH_w1 (A := land (shapeBin c 1) (argsIn w (nthc c (numeralM 2)))) hwf) hab)
    exact PrfH.mp _ _ _ (prf_to_prfH (refl_shapeBin_imp c) _) (PrfH_and_intro hsb hTLb)

/-- Version `Prf → Prf` (la moneda que consume `paso2_caso_forall` tal como esta hoy). -/
theorem descenso_apply (w c : Term) (h : Prf (isTC1 w c)) : Prf (targetLift c) :=
  prf_mp (descenso w c) h

/-! ## §C7 · CONTROLES NEGATIVOS -/

/-- El enunciado del descenso NO es una reflexividad disfrazada. -/
example (s : Term) : True := by
  fail_if_success
    exact (rfl : liftcT (termCode zero) (tcFn s) = tcFn (liftc zero s))
  trivial

example (b : Term) : True := by
  fail_if_success
    exact (rfl : liftscT (termCode zero) (tcFn b) = tcFn (liftsc zero b))
  trivial

/-- La guarda NO es vacua: `sondeos/ClausuraLiftSinWTs.lean:1010` (`prf_isTC1_tcodes`)
    exhibe testigo para TODO termino real. Aqui el control es que el descenso se puede
    DISPARAR con testigo ABIERTO — `#0` de testigo y `#1` de codigo, que es lo que
    entrega un `∃`‑elim. -/
example : Prf (Formula.impl (isTC1 (.var 0) (.var 1)) (targetLift (.var 1))) :=
  descenso (.var 0) (.var 1)

/-- Y la mitad de listas tambien, con testigo ABIERTO. -/
example : Prf (Formula.impl (land (wfAll1 (.var 0)) (argsIn (.var 0) (.var 1)))
    (targetLiftsc (.var 1))) := desc_lista (.var 0) (.var 1)

/-- CONTROL de que el descenso ATA con el consumidor: la conclusion del descenso es
    LITERALMENTE la hipotesis `hLift` de `paso2_caso_forall`. -/
example (w s : Term) (h : Prf (isTC1 w s)) :
    Prf (provFromCode (eqc (liftcT (termCode zero) (tcFn s)) (tcFn (liftc zero s)))) :=
  descenso_apply w s h


/-! ## §C8 · NO VACUIDAD DE LA GUARDA, y el PAYOFF NETO

    ⚠️ Obligatorio: `descenso` anade la guarda `isTC1 w c`. Se comprueba que es
    SATISFACIBLE por codigos REALES — no es un teorema verdadero y vacio. -/

/-- **La guarda NO es vacua**: todo termino real tiene testigo COMPUTABLE, y es UNA SOLA
    lista (`tcodes1 t`). -/
example (t : Term) : Prf (isTC1 (objList (tcodes1 t)) (termCodeM t)) := prf_isTC1_tcodes t

/-- **PAYOFF NETO**: para TODO termino REAL, el `hLift` que le falta a
    `paso2_caso_forall` queda PROBADO **por la ruta del descenso**, con testigo explicito.
    (Es la comprobacion de que la guarda y el descenso encajan de punta a punta.) -/
theorem hLift_para_todo_termino (t : Term) : Prf (targetLift (termCodeM t)) :=
  descenso_apply (objList (tcodes1 t)) (termCodeM t) (prf_isTC1_tcodes t)
end DescCons

/-! # §D · VERIFICACION ADVERSARIAL (nuevo; no toca nada de §A-§C) -/

namespace CritDesc
open DescCons

/-! ## §D1 · ABSTRACCION: `w` y `s` son variables `Term` LIBRES, y NO hay hipotesis extra -/

/-- El enunciado PEDIDO, literal y universalmente cuantificado sobre `w` y `s`. -/
example : ∀ w s : Term, Prf (isTC1 w s) → Prf (targetLift s) := descenso_apply

/-- Forma implicativa; `w`/`c` abstractos, ninguna premisa adicional. -/
example : ∀ w c : Term, Prf (Formula.impl (isTC1 w c) (targetLift c)) := descenso

/-- La conclusion es LITERALMENTE el `hLift` de `sondeos/Paso2CasoForall.lean:507`. -/
example : ∀ w s : Term, Prf (isTC1 w s) →
    Prf (provFromCode (eqc (liftcT (termCode zero) (tcFn s)) (tcFn (liftc zero s)))) :=
  descenso_apply

/-- La gemela sobre listas, `w`/`Y` abstractos. -/
example : ∀ w Y : Term, Prf (Formula.impl (land (wfAll1 w) (argsIn w Y)) (targetLiftsc Y)) :=
  desc_lista

/-- Transporta a CUALQUIER contexto: es lo que hara falta aguas abajo. -/
example (Gm : List Formula) (w c : Term) :
    PrfH Gm (Formula.impl (isTC1 w c) (targetLift c)) := prf_to_prfH (descenso w c) Gm

/-! ## §D2 · SATISFACIBILIDAD con terminos REALES que EJERCITAN la rama recursiva -/

def tf : Term := Term.func "f" [Term.var 0]
def tg : Term := Term.func "g" [Term.func "f" [Term.var 0], Term.var 1]

example : Prf (isTC1 (objList (tcodes1 tf)) (termCodeM tf)) := prf_isTC1_tcodes tf
example : Prf (isTC1 (objList (tcodes1 tg)) (termCodeM tg)) := prf_isTC1_tcodes tg
example : Prf (targetLift (termCodeM tf)) := hLift_para_todo_termino tf
example : Prf (targetLift (termCodeM tg)) := hLift_para_todo_termino tg

/-! ## §D3 · LA GUARDA DE LA GEMELA (`argsIn`; desviacion 1) ES SATISFACIBLE -/

theorem argsIn_real (s : String) (ts : List Term) :
    Prf (argsIn (objList (tcodes1 (Term.func s ts))) (termsCodeM ts)) := by
  have hWl : ∀ c : Nat, liftTerm c (objList (tcodes1 (Term.func s ts)))
      = objList (tcodes1 (Term.func s ts)) := fun c =>
    liftTerm_objList c _ (fun x hx => (closed_mem_tcodes1 _ x hx).1 c)
  have hWs : ∀ (v : Nat) (u : Term), substTerm v u (objList (tcodes1 (Term.func s ts)))
      = objList (tcodes1 (Term.func s ts)) := fun v u =>
    substTerm_objList v u _ (fun x hx => (closed_mem_tcodes1 _ x hx).2 v u)
  refine prf_argsIn_of_closed _ (termsCodeM ts) ts.length (hWl 0)
    (liftTerm_termsCodeM 0 ts) hWs (fun v u => substTerm_termsCodeM v u ts)
    (prf_lenc_termsCodeM ts) ?_
  intro k hk
  obtain ⟨u, hu⟩ : ∃ u, ts[k]? = some u := ⟨ts[k], getElem?_pos ts k hk⟩
  refine prf_congr_In_left (prf_eq_symm (prf_nthc_termsCodeM ts k u hu)) ?_
  refine prf_In_objList _ (termCodeM u) ?_
  simp only [tcodes1]
  exact List.Mem.tail _ (mem_tcodes1s_of_mem ts u (mem_of_getElem? ts k u hu))

/-- `desc_lista` NO es un teorema verdadero y VACIO: su guarda se dispara con testigo real. -/
theorem targetLiftsc_real (s : String) (ts : List Term) :
    Prf (targetLiftsc (termsCodeM ts)) :=
  prf_mp (desc_lista (objList (tcodes1 (Term.func s ts))) (termsCodeM ts))
    (prf_and_intro (prf_and_elim_left (prf_isTC1_tcodes (Term.func s ts))) (argsIn_real s ts))

example : Prf (targetLiftsc (termsCodeM [Term.var 0, Term.func "h" [Term.var 1]])) :=
  targetLiftsc_real "f" _

/-! ## §D4 · LA INDUCCION ES LA DE VERDAD: `w` va DENTRO de `Φ`, y el gate se DESCARGA -/

/-- El testigo esta CUANTIFICADO DENTRO: tras el binder, `#0` es `w` y `#1` el codigo. -/
example : DPHI = Formula.forall (Formula.impl
    (land (wfAll1 (Term.var 0)) (argsIn (Term.var 0) (Term.var 1)))
    (targetLiftsc (Term.var 1))) := rfl

/-- `hΦ` se PRUEBA (no se asume, ni se esquiva con clausura sobre `w`). -/
example : liftFormula 1 DPHI = DPHI := DPHI_lift

/-- Y `prf_strong_induction` se usa DE VERDAD, con ese `Φ` y ese gate. -/
example (Y : Term) : Prf (substFormula 0 Y DPHI) :=
  prf_strong_induction DPHI DPHI_lift DPHI_step Y

/-! ## §D5 · CONTROLES NEGATIVOS: nada de esto es `rfl` -/

example (s : Term) : True := by
  fail_if_success exact (rfl : liftcT (termCode zero) (tcFn s) = tcFn (liftc zero s))
  trivial

example (b : Term) : True := by
  fail_if_success exact (rfl : liftscT (termCode zero) (tcFn b) = tcFn (liftsc zero b))
  trivial

/-- `isTC1` NO es la formula trivial: no colapsa a su segundo conyunto. -/
example (w c : Term) : True := by
  fail_if_success exact (rfl : isTC1 w c = In c w)
  trivial

end CritDesc

#print axioms CritDesc.argsIn_real
#print axioms CritDesc.targetLiftsc_real

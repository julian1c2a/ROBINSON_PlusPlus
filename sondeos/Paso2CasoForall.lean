/- # CritPaso1 — FUSIÓN PROPUESTA del PASO 1 del frente ③ (`pcc_eval_substfc`).

   Base: `Probe/Ctor_desdec.lean` (§0-§3 completos, incluida la prueba de fuego (c)).
   Injertos:
     * `prf_congr_funcc3`  ← `Probe/Ctor_directo.lean:94`  (deduplica las 3 congruencias ternarias)
     * congruencias INTERNAS `pcc_congr_*_code` ← patrón `Meta/CodeCtorKit.lean:267,286`
       (la pieza que NINGUNO de los tres ficheros tiene y que el PASO 2 consume)
     * fuego (a)+(b): composición de (c) con el KIT (`pcc_dot_un_symm` + `pcc_eq_trans_code`)
     * conmutación META `liftTerm`/`substTerm` para los SEIS (desdec sólo tenía 2)
   Descartado de `Ctor_generico.lean`: la capa `fn1T/fn2T/fn3T` (18 lemas de indirección para
   un conjunto CERRADO de 6 símbolos) y los `liftc_inv_fn*T` (código muerto: su hipótesis
   `∀c, Prf (liftc c X =eq X)` no se puede descargar hoy).

   ⚠️ CERO axiomas de Lean, cero `sorry`. `substfcT`/`liftcT`/… son DEFINICIONES y nada más:
   ninguna ecuación de recursión suya se postula (eso sería `ax_tc_substfc`, INCONSISTENTE). -/
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

set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

namespace Paso2

/-! ## §0 · Piezas GENÉRICAS que faltaban en producción -/

/-- `substtc` sobre un `funcc` de **tres** argumentos (hueco de `prf_substtc_funcc1/2`). -/
theorem prf_substtc_funcc3 (v W sc x y z : Term) :
    Prf (substtc v W (funcc sc (cons x (cons y (cons z nil))))
      =eq funcc sc (cons (substtc v W x) (cons (substtc v W y) (cons (substtc v W z) nil)))) :=
  prf_eq_trans (prf_substtc_func v W sc (cons x (cons y (cons z nil))))
    (prf_congr_funcc2
      (prf_eq_trans (prf_substtsc_cons v W x (cons y (cons z nil)))
        (prf_congr_cons_tail
          (prf_eq_trans (prf_substtsc_cons v W y (cons z nil))
            (prf_congr_cons_tail
              (prf_eq_trans (prf_substtsc_cons v W z nil)
                (prf_congr_cons_tail (prf_substtsc_nil v W))))))))

theorem prf_liftc_funcc2 (c sc x y : Term) :
    Prf (liftc c (funcc sc (cons x (cons y nil)))
      =eq funcc sc (cons (liftc c x) (cons (liftc c y) nil))) :=
  prf_eq_trans (prf_liftc_func c sc (cons x (cons y nil)))
    (prf_congr_funcc2
      (prf_eq_trans (prf_liftsc_cons c x (cons y nil))
        (prf_congr_cons_tail
          (prf_eq_trans (prf_liftsc_cons c y nil)
            (prf_congr_cons_tail (prf_liftsc_nil c))))))

theorem prf_liftc_funcc3 (c sc x y z : Term) :
    Prf (liftc c (funcc sc (cons x (cons y (cons z nil))))
      =eq funcc sc (cons (liftc c x) (cons (liftc c y) (cons (liftc c z) nil)))) :=
  prf_eq_trans (prf_liftc_func c sc (cons x (cons y (cons z nil))))
    (prf_congr_funcc2
      (prf_eq_trans (prf_liftsc_cons c x (cons y (cons z nil)))
        (prf_congr_cons_tail
          (prf_eq_trans (prf_liftsc_cons c y (cons z nil))
            (prf_congr_cons_tail
              (prf_eq_trans (prf_liftsc_cons c z nil)
                (prf_congr_cons_tail (prf_liftsc_nil c))))))))

/-- INJERTO de `Ctor_directo.lean:94` — deduplica las tres congruencias ternarias. -/
theorem prf_congr_funcc3 {sc x x' y y' z z' : Term}
    (hx : Prf (x =eq x')) (hy : Prf (y =eq y')) (hz : Prf (z =eq z')) :
    Prf (funcc sc (cons x (cons y (cons z nil)))
      =eq funcc sc (cons x' (cons y' (cons z' nil)))) :=
  prf_congr_funcc2 (prf_eq_trans (prf_congr_cons_head hx)
    (prf_congr_cons_tail (prf_eq_trans (prf_congr_cons_head hy)
      (prf_congr_cons_tail (prf_congr_cons_head hz)))))

/-! ## §1 · Los SEIS constructores de código (DEFINICIONES, sin ecuaciones postuladas) -/

def substfcT (v s f : Term) : Term :=
  funcc (strCode "substfc") (cons v (cons s (cons f nil)))
def substtcT (v s t : Term) : Term :=
  funcc (strCode "substtc") (cons v (cons s (cons t nil)))
def substtscT (v s ts : Term) : Term :=
  funcc (strCode "substtsc") (cons v (cons s (cons ts nil)))
def liftcT (c t : Term) : Term := funcc (strCode "liftc") (cons c (cons t nil))
def liftfcT (c f : Term) : Term := funcc (strCode "liftfc") (cons c (cons f nil))
def liftscT (c ts : Term) : Term := funcc (strCode "liftsc") (cons c (cons ts nil))

/-! ### Puentes `_termCode`, por `rfl` -/

theorem substfcT_termCode (v s f : Term) :
    substfcT (termCode v) (termCode s) (termCode f) = termCode (substfc v s f) := rfl
theorem substtcT_termCode (v s t : Term) :
    substtcT (termCode v) (termCode s) (termCode t) = termCode (substtc v s t) := rfl
theorem substtscT_termCode (v s ts : Term) :
    substtscT (termCode v) (termCode s) (termCode ts) = termCode (substtsc v s ts) := rfl
theorem liftcT_termCode (c t : Term) :
    liftcT (termCode c) (termCode t) = termCode (liftc c t) := rfl
theorem liftfcT_termCode (c f : Term) :
    liftfcT (termCode c) (termCode f) = termCode (liftfc c f) := rfl
theorem liftscT_termCode (c ts : Term) :
    liftscT (termCode c) (termCode ts) = termCode (liftsc c ts) := rfl

/-! ### Congruencias META (vía el injerto `prf_congr_funcc3`) -/

theorem prf_congr_substfcT {v v' s s' f f' : Term}
    (hv : Prf (v =eq v')) (hs : Prf (s =eq s')) (hf : Prf (f =eq f')) :
    Prf (substfcT v s f =eq substfcT v' s' f') := prf_congr_funcc3 hv hs hf
theorem prf_congr_substtcT {v v' s s' t t' : Term}
    (hv : Prf (v =eq v')) (hs : Prf (s =eq s')) (ht : Prf (t =eq t')) :
    Prf (substtcT v s t =eq substtcT v' s' t') := prf_congr_funcc3 hv hs ht
theorem prf_congr_substtscT {v v' s s' t t' : Term}
    (hv : Prf (v =eq v')) (hs : Prf (s =eq s')) (ht : Prf (t =eq t')) :
    Prf (substtscT v s t =eq substtscT v' s' t') := prf_congr_funcc3 hv hs ht
theorem prf_congr_liftcT {c c' t t' : Term} (hc : Prf (c =eq c')) (ht : Prf (t =eq t')) :
    Prf (liftcT c t =eq liftcT c' t') :=
  prf_congr_funcc2 (prf_eq_trans (prf_congr_cons_head hc)
    (prf_congr_cons_tail (prf_congr_cons_head ht)))
theorem prf_congr_liftfcT {c c' t t' : Term} (hc : Prf (c =eq c')) (ht : Prf (t =eq t')) :
    Prf (liftfcT c t =eq liftfcT c' t') :=
  prf_congr_funcc2 (prf_eq_trans (prf_congr_cons_head hc)
    (prf_congr_cons_tail (prf_congr_cons_head ht)))
theorem prf_congr_liftscT {c c' t t' : Term} (hc : Prf (c =eq c')) (ht : Prf (t =eq t')) :
    Prf (liftscT c t =eq liftscT c' t') :=
  prf_congr_funcc2 (prf_eq_trans (prf_congr_cons_head hc)
    (prf_congr_cons_tail (prf_congr_cons_head ht)))

/-! ### `substtc` / `liftc` atraviesan (nivel ARBITRARIO) -/

theorem prf_substtc_substfcT (v W x y z : Term) :
    Prf (substtc v W (substfcT x y z)
      =eq substfcT (substtc v W x) (substtc v W y) (substtc v W z)) :=
  prf_substtc_funcc3 v W (strCode "substfc") x y z
theorem prf_substtc_substtcT (v W x y z : Term) :
    Prf (substtc v W (substtcT x y z)
      =eq substtcT (substtc v W x) (substtc v W y) (substtc v W z)) :=
  prf_substtc_funcc3 v W (strCode "substtc") x y z
theorem prf_substtc_substtscT (v W x y z : Term) :
    Prf (substtc v W (substtscT x y z)
      =eq substtscT (substtc v W x) (substtc v W y) (substtc v W z)) :=
  prf_substtc_funcc3 v W (strCode "substtsc") x y z
theorem prf_substtc_liftcT (v W x y : Term) :
    Prf (substtc v W (liftcT x y) =eq liftcT (substtc v W x) (substtc v W y)) :=
  prf_substtc_funcc2 v W (strCode "liftc") x y
theorem prf_substtc_liftfcT (v W x y : Term) :
    Prf (substtc v W (liftfcT x y) =eq liftfcT (substtc v W x) (substtc v W y)) :=
  prf_substtc_funcc2 v W (strCode "liftfc") x y
theorem prf_substtc_liftscT (v W x y : Term) :
    Prf (substtc v W (liftscT x y) =eq liftscT (substtc v W x) (substtc v W y)) :=
  prf_substtc_funcc2 v W (strCode "liftsc") x y

theorem prf_liftc_substfcT (c x y z : Term) :
    Prf (liftc c (substfcT x y z) =eq substfcT (liftc c x) (liftc c y) (liftc c z)) :=
  prf_liftc_funcc3 c (strCode "substfc") x y z
theorem prf_liftc_substtcT (c x y z : Term) :
    Prf (liftc c (substtcT x y z) =eq substtcT (liftc c x) (liftc c y) (liftc c z)) :=
  prf_liftc_funcc3 c (strCode "substtc") x y z
theorem prf_liftc_substtscT (c x y z : Term) :
    Prf (liftc c (substtscT x y z) =eq substtscT (liftc c x) (liftc c y) (liftc c z)) :=
  prf_liftc_funcc3 c (strCode "substtsc") x y z
theorem prf_liftc_liftcT (c x y : Term) :
    Prf (liftc c (liftcT x y) =eq liftcT (liftc c x) (liftc c y)) :=
  prf_liftc_funcc2 c (strCode "liftc") x y
theorem prf_liftc_liftfcT (c x y : Term) :
    Prf (liftc c (liftfcT x y) =eq liftfcT (liftc c x) (liftc c y)) :=
  prf_liftc_funcc2 c (strCode "liftfc") x y
theorem prf_liftc_liftscT (c x y : Term) :
    Prf (liftc c (liftscT x y) =eq liftscT (liftc c x) (liftc c y)) :=
  prf_liftc_funcc2 c (strCode "liftsc") x y

/-! ### Invariancias `substtc` a nivel `zero` (la forma que consumen los Leibniz internos) -/

theorem substtc_inv_substfcT {X Y Z : Term}
    (hX : ∀ W, Prf (substtc zero W X =eq X)) (hY : ∀ W, Prf (substtc zero W Y =eq Y))
    (hZ : ∀ W, Prf (substtc zero W Z =eq Z)) :
    ∀ W, Prf (substtc zero W (substfcT X Y Z) =eq substfcT X Y Z) := fun W =>
  prf_eq_trans (prf_substtc_substfcT zero W X Y Z) (prf_congr_substfcT (hX W) (hY W) (hZ W))
theorem substtc_inv_substtcT {X Y Z : Term}
    (hX : ∀ W, Prf (substtc zero W X =eq X)) (hY : ∀ W, Prf (substtc zero W Y =eq Y))
    (hZ : ∀ W, Prf (substtc zero W Z =eq Z)) :
    ∀ W, Prf (substtc zero W (substtcT X Y Z) =eq substtcT X Y Z) := fun W =>
  prf_eq_trans (prf_substtc_substtcT zero W X Y Z) (prf_congr_substtcT (hX W) (hY W) (hZ W))
theorem substtc_inv_substtscT {X Y Z : Term}
    (hX : ∀ W, Prf (substtc zero W X =eq X)) (hY : ∀ W, Prf (substtc zero W Y =eq Y))
    (hZ : ∀ W, Prf (substtc zero W Z =eq Z)) :
    ∀ W, Prf (substtc zero W (substtscT X Y Z) =eq substtscT X Y Z) := fun W =>
  prf_eq_trans (prf_substtc_substtscT zero W X Y Z) (prf_congr_substtscT (hX W) (hY W) (hZ W))
theorem substtc_inv_liftcT {X Y : Term}
    (hX : ∀ W, Prf (substtc zero W X =eq X)) (hY : ∀ W, Prf (substtc zero W Y =eq Y)) :
    ∀ W, Prf (substtc zero W (liftcT X Y) =eq liftcT X Y) := fun W =>
  prf_eq_trans (prf_substtc_liftcT zero W X Y) (prf_congr_liftcT (hX W) (hY W))
theorem substtc_inv_liftfcT {X Y : Term}
    (hX : ∀ W, Prf (substtc zero W X =eq X)) (hY : ∀ W, Prf (substtc zero W Y =eq Y)) :
    ∀ W, Prf (substtc zero W (liftfcT X Y) =eq liftfcT X Y) := fun W =>
  prf_eq_trans (prf_substtc_liftfcT zero W X Y) (prf_congr_liftfcT (hX W) (hY W))
theorem substtc_inv_liftscT {X Y : Term}
    (hX : ∀ W, Prf (substtc zero W X =eq X)) (hY : ∀ W, Prf (substtc zero W Y =eq Y)) :
    ∀ W, Prf (substtc zero W (liftscT X Y) =eq liftscT X Y) := fun W =>
  prf_eq_trans (prf_substtc_liftscT zero W X Y) (prf_congr_liftscT (hX W) (hY W))

/-! ### Conmutación META con `liftTerm`/`substTerm` — LOS SEIS (desdec sólo tenía 2) -/

theorem liftTerm_substfcT (k : Nat) (v s f : Term) :
    liftTerm k (substfcT v s f) = substfcT (liftTerm k v) (liftTerm k s) (liftTerm k f) := by
  simp only [substfcT, funcc, cons, nil, zero, succ, liftTerm, liftTerms, liftTerm_strCode]
theorem substTerm_substfcT (k : Nat) (u v s f : Term) :
    substTerm k u (substfcT v s f)
      = substfcT (substTerm k u v) (substTerm k u s) (substTerm k u f) := by
  simp only [substfcT, funcc, cons, nil, zero, succ, substTerm, substTerms, substTerm_strCode]
theorem liftTerm_substtcT (k : Nat) (v s f : Term) :
    liftTerm k (substtcT v s f) = substtcT (liftTerm k v) (liftTerm k s) (liftTerm k f) := by
  simp only [substtcT, funcc, cons, nil, zero, succ, liftTerm, liftTerms, liftTerm_strCode]
theorem substTerm_substtcT (k : Nat) (u v s f : Term) :
    substTerm k u (substtcT v s f)
      = substtcT (substTerm k u v) (substTerm k u s) (substTerm k u f) := by
  simp only [substtcT, funcc, cons, nil, zero, succ, substTerm, substTerms, substTerm_strCode]
theorem liftTerm_substtscT (k : Nat) (v s f : Term) :
    liftTerm k (substtscT v s f) = substtscT (liftTerm k v) (liftTerm k s) (liftTerm k f) := by
  simp only [substtscT, funcc, cons, nil, zero, succ, liftTerm, liftTerms, liftTerm_strCode]
theorem substTerm_substtscT (k : Nat) (u v s f : Term) :
    substTerm k u (substtscT v s f)
      = substtscT (substTerm k u v) (substTerm k u s) (substTerm k u f) := by
  simp only [substtscT, funcc, cons, nil, zero, succ, substTerm, substTerms, substTerm_strCode]
theorem liftTerm_liftcT (k : Nat) (c t : Term) :
    liftTerm k (liftcT c t) = liftcT (liftTerm k c) (liftTerm k t) := by
  simp only [liftcT, funcc, cons, nil, zero, succ, liftTerm, liftTerms, liftTerm_strCode]
theorem substTerm_liftcT (k : Nat) (u c t : Term) :
    substTerm k u (liftcT c t) = liftcT (substTerm k u c) (substTerm k u t) := by
  simp only [liftcT, funcc, cons, nil, zero, succ, substTerm, substTerms, substTerm_strCode]
theorem liftTerm_liftfcT (k : Nat) (c t : Term) :
    liftTerm k (liftfcT c t) = liftfcT (liftTerm k c) (liftTerm k t) := by
  simp only [liftfcT, funcc, cons, nil, zero, succ, liftTerm, liftTerms, liftTerm_strCode]
theorem substTerm_liftfcT (k : Nat) (u c t : Term) :
    substTerm k u (liftfcT c t) = liftfcT (substTerm k u c) (substTerm k u t) := by
  simp only [liftfcT, funcc, cons, nil, zero, succ, substTerm, substTerms, substTerm_strCode]
theorem liftTerm_liftscT (k : Nat) (c t : Term) :
    liftTerm k (liftscT c t) = liftscT (liftTerm k c) (liftTerm k t) := by
  simp only [liftscT, funcc, cons, nil, zero, succ, liftTerm, liftTerms, liftTerm_strCode]
theorem substTerm_liftscT (k : Nat) (u c t : Term) :
    substTerm k u (liftscT c t) = liftscT (substTerm k u c) (substTerm k u t) := by
  simp only [liftscT, funcc, cons, nil, zero, succ, substTerm, substTerms, substTerm_strCode]

/-! ## §2 · Utilidades de NIVEL (`substtc` a nivel `numeral v` arbitrario) -/

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

/-! ## §3 · PRUEBA DE FUEGO (c): la instancia INTERNA de `ax_substfc_forall` -/

def AXF_BODY : Formula :=
  substfc (.var 2) (.var 1) (forallc (.var 0))
    =eq forallc (substfc (succ (.var 2)) (liftc zero (.var 1)) (.var 0))

theorem AXF_BODY_ok : ax_substfc_forall = forall_3 AXF_BODY := rfl

theorem pcc_substfc_forall_dot (a b f : Term) :
    Prf (provFromCode (eqCodeFn
      (substfcT (tcFn a) (tcFn b) (unT 6 (tcFn f)))
      (unT 6 (substfcT (succcT (tcFn a)) (liftcT (termCode zero) (tcFn b)) (tcFn f))))) := by
  let W2 : Term := liftc zero (liftc zero (tcFn a))
  let W1 : Term := liftc zero (tcFn b)
  let W0 : Term := tcFn f
  have hin : Prf (substfc (succ (succ zero)) W2 (formCode AXF_BODY)
      =eq eqCodeFn
        (substfcT W2 (varc (numeral 1)) (unT 6 (varc (numeral 0))))
        (unT 6 (substfcT (succcT W2) (liftcT (termCode zero) (varc (numeral 1)))
          (varc (numeral 0))))) :=
    prf_substfc_arith_open 2 W2 AXF_BODY
  have hA2 : Prf (W2 =eq tcFn a) :=
    prf_eq_trans (prf_congr_liftc (prf_liftc_tcFn a)) (prf_liftc_tcFn a)
  have hnorm : Prf (eqCodeFn
        (substfcT W2 (varc (numeral 1)) (unT 6 (varc (numeral 0))))
        (unT 6 (substfcT (succcT W2) (liftcT (termCode zero) (varc (numeral 1)))
          (varc (numeral 0))))
      =eq eqCodeFn
        (substfcT (tcFn a) (varc (numeral 1)) (unT 6 (varc (numeral 0))))
        (unT 6 (substfcT (succcT (tcFn a)) (liftcT (termCode zero) (varc (numeral 1)))
          (varc (numeral 0))))) :=
    prf_congr_eqCodeFn
      (prf_congr_substfcT hA2 (prf_refl _) (prf_refl _))
      (prf_congr_unT (prf_congr_substfcT (prf_congr_succcT hA2) (prf_refl _) (prf_refl _)))
  have hv1 : Prf (substtc (succ zero) W1 (varc (numeral 1)) =eq tcFn b) :=
    prf_eq_trans (prf_mp (prf_substtc_var_eq (succ zero) W1 (numeral 1)) (prf_refl _))
      (prf_liftc_tcFn b)
  have hv0 : Prf (substtc (succ zero) W1 (varc (numeral 0)) =eq varc (numeral 0)) :=
    prf_mp (prf_substtc_var_lt (succ zero) W1 (numeral 0)) (prf_zero_lt_succ zero)
  have ha1 : Prf (substtc (succ zero) W1 (tcFn a) =eq tcFn a) := prf_substtc_tcFn_at 1 W1 a
  have hmid : Prf (substfc (succ zero) W1 (eqCodeFn
        (substfcT (tcFn a) (varc (numeral 1)) (unT 6 (varc (numeral 0))))
        (unT 6 (substfcT (succcT (tcFn a)) (liftcT (termCode zero) (varc (numeral 1)))
          (varc (numeral 0)))))
      =eq eqCodeFn
        (substfcT (tcFn a) (tcFn b) (unT 6 (varc (numeral 0))))
        (unT 6 (substfcT (succcT (tcFn a)) (liftcT (termCode zero) (tcFn b))
          (varc (numeral 0))))) := by
    refine prf_eq_trans (prf_substfc_eq (succ zero) W1 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_substfcT (succ zero) W1 _ _ _) ?_
      refine prf_congr_substfcT ha1 hv1 ?_
      exact prf_eq_trans (prf_substtc_unT_at 6 1 W1 (varc (numeral 0))) (prf_congr_unT hv0)
    · refine prf_eq_trans (prf_substtc_unT_at 6 1 W1 _) ?_
      refine prf_congr_unT ?_
      refine prf_eq_trans (prf_substtc_substfcT (succ zero) W1 _ _ _) ?_
      refine prf_congr_substfcT ?_ ?_ hv0
      · exact prf_eq_trans (prf_substtc_succcT (succ zero) W1 (tcFn a)) (prf_congr_succcT ha1)
      · exact prf_eq_trans (prf_substtc_liftcT (succ zero) W1 _ _)
          (prf_congr_liftcT (prf_substtc_termCode_zero 1 W1) hv1)
  have hout : Prf (substfc zero W0 (eqCodeFn
        (substfcT (tcFn a) (tcFn b) (unT 6 (varc (numeral 0))))
        (unT 6 (substfcT (succcT (tcFn a)) (liftcT (termCode zero) (tcFn b))
          (varc (numeral 0)))))
      =eq eqCodeFn
        (substfcT (tcFn a) (tcFn b) (unT 6 (tcFn f)))
        (unT 6 (substfcT (succcT (tcFn a)) (liftcT (termCode zero) (tcFn b)) (tcFn f)))) := by
    refine prf_eq_trans (prf_substfc_eq zero W0 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_substfcT zero W0 _ _ _) ?_
      refine prf_congr_substfcT (prf_substtc_tcFn W0 a) (prf_substtc_tcFn W0 b) ?_
      exact prf_eq_trans (prf_substtc_unT_at 6 0 W0 (varc (numeral 0)))
        (prf_congr_unT (prf_substtc_varc0 W0))
    · refine prf_eq_trans (prf_substtc_unT_at 6 0 W0 _) ?_
      refine prf_congr_unT ?_
      refine prf_eq_trans (prf_substtc_substfcT zero W0 _ _ _) ?_
      refine prf_congr_substfcT ?_ ?_ (prf_substtc_varc0 W0)
      · exact prf_eq_trans (prf_substtc_succcT zero W0 (tcFn a))
          (prf_congr_succcT (prf_substtc_tcFn W0 a))
      · exact prf_eq_trans (prf_substtc_liftcT zero W0 _ _)
          (prf_congr_liftcT (prf_substtc_termCode_zero 0 W0) (prf_substtc_tcFn W0 b))
  have hchain : Prf (substfc zero W0 (substfc (succ zero) W1
      (substfc (succ (succ zero)) W2 (formCode AXF_BODY)))
      =eq eqCodeFn
        (substfcT (tcFn a) (tcFn b) (unT 6 (tcFn f)))
        (unT 6 (substfcT (succcT (tcFn a)) (liftcT (termCode zero) (tcFn b)) (tcFn f)))) :=
    prf_eq_trans (prf_congr_substfc_arg3
      (prf_eq_trans (prf_congr_substfc_arg3 (prf_eq_trans hin hnorm)) hmid)) hout
  exact prf_mp (prf_provCode_congr hchain)
    (pcc_axiom_inst3 AXF_BODY (show ax_substfc_forall ∈ axioms by simp [axioms])
      (tcFn a) (tcFn b) (tcFn f))

/-! ## §4 · LA PIEZA QUE FALTABA EN LOS TRES: congruencias INTERNAS (dentro de `Prov`)

Patrón `pcc_congr_binT_1_code` / `pcc_congr_unT_code` (`Meta/CodeCtorKit.lean:267,286`).
Sin ellas no hay forma de reescribir un subtérmino de `substfcT`/`liftcT` DENTRO de `Prov`,
que es exactamente lo que pide el paso inductivo del PASO 2. -/

theorem pcc_congr_substfcT_arg1_code (B C X Y : Term)
    (hB : ∀ W, Prf (substtc zero W B =eq B)) (hC : ∀ W, Prf (substtc zero W C =eq C))
    (hX : ∀ W, Prf (substtc zero W X =eq X)) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (substfcT X B C) (substfcT Y B C))) := by
  let Ac : Term := eqc (substfcT X B C) (substfcT (varc (numeral 0)) B C)
  have hcomp : ∀ w : Term, Prf (substfc zero w Ac =eq eqc (substfcT X B C) (substfcT w B C)) := by
    intro w
    refine prf_eq_trans (prf_substfc_eq zero w (substfcT X B C)
      (substfcT (varc (numeral 0)) B C)) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · exact prf_eq_trans (prf_substtc_substfcT zero w X B C)
        (prf_congr_substfcT (hX w) (hB w) (hC w))
    · exact prf_eq_trans (prf_substtc_substfcT zero w (varc (numeral 0)) B C)
        (prf_congr_substfcT (prf_substtc_varc0 w) (hB w) (hC w))
  have hAX : Prf (provFromCode (substfc zero X Ac)) :=
    prf_mp (prf_provCode_congr (prf_eq_symm (hcomp X)))
      (prf_provFromCode_eqCodeFn_refl (substfcT X B C))
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcomp Y)) _)
    (PrfH_leibniz_apply Ac X Y (prfH_hyp_self _) (prf_to_prfH hAX _))

theorem pcc_congr_substfcT_arg2_code (A C X Y : Term)
    (hA : ∀ W, Prf (substtc zero W A =eq A)) (hC : ∀ W, Prf (substtc zero W C =eq C))
    (hX : ∀ W, Prf (substtc zero W X =eq X)) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (substfcT A X C) (substfcT A Y C))) := by
  let Ac : Term := eqc (substfcT A X C) (substfcT A (varc (numeral 0)) C)
  have hcomp : ∀ w : Term, Prf (substfc zero w Ac =eq eqc (substfcT A X C) (substfcT A w C)) := by
    intro w
    refine prf_eq_trans (prf_substfc_eq zero w (substfcT A X C)
      (substfcT A (varc (numeral 0)) C)) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · exact prf_eq_trans (prf_substtc_substfcT zero w A X C)
        (prf_congr_substfcT (hA w) (hX w) (hC w))
    · exact prf_eq_trans (prf_substtc_substfcT zero w A (varc (numeral 0)) C)
        (prf_congr_substfcT (hA w) (prf_substtc_varc0 w) (hC w))
  have hAX : Prf (provFromCode (substfc zero X Ac)) :=
    prf_mp (prf_provCode_congr (prf_eq_symm (hcomp X)))
      (prf_provFromCode_eqCodeFn_refl (substfcT A X C))
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcomp Y)) _)
    (PrfH_leibniz_apply Ac X Y (prfH_hyp_self _) (prf_to_prfH hAX _))

theorem pcc_congr_substfcT_arg3_code (A B X Y : Term)
    (hA : ∀ W, Prf (substtc zero W A =eq A)) (hB : ∀ W, Prf (substtc zero W B =eq B))
    (hX : ∀ W, Prf (substtc zero W X =eq X)) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (substfcT A B X) (substfcT A B Y))) := by
  let Ac : Term := eqc (substfcT A B X) (substfcT A B (varc (numeral 0)))
  have hcomp : ∀ w : Term, Prf (substfc zero w Ac =eq eqc (substfcT A B X) (substfcT A B w)) := by
    intro w
    refine prf_eq_trans (prf_substfc_eq zero w (substfcT A B X)
      (substfcT A B (varc (numeral 0)))) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · exact prf_eq_trans (prf_substtc_substfcT zero w A B X)
        (prf_congr_substfcT (hA w) (hB w) (hX w))
    · exact prf_eq_trans (prf_substtc_substfcT zero w A B (varc (numeral 0)))
        (prf_congr_substfcT (hA w) (hB w) (prf_substtc_varc0 w))
  have hAX : Prf (provFromCode (substfc zero X Ac)) :=
    prf_mp (prf_provCode_congr (prf_eq_symm (hcomp X)))
      (prf_provFromCode_eqCodeFn_refl (substfcT A B X))
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcomp Y)) _)
    (PrfH_leibniz_apply Ac X Y (prfH_hyp_self _) (prf_to_prfH hAX _))

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

/-! ## §5 · FUEGO (a)+(b): (c) compuesta con el KIT — la forma DOTADA del paso inductivo -/

/-- (a) `pcc_eq_trans_code` + (b) el KIT (`pcc_dot_un_symm`) + §4. -/
theorem fuego_ab (a b f : Term) :
    Prf (provFromCode (eqCodeFn
      (substfcT (tcFn a) (tcFn b) (tcFn (forallc f)))
      (unT 6 (substfcT (succcT (tcFn a)) (liftcT (termCode zero) (tcFn b)) (tcFn f))))) := by
  have hdot : Prf (provFromCode (eqc (tcFn (forallc f)) (unT 6 (tcFn f)))) :=
    pcc_dot_un_symm 6 f
  have hcongr : Prf (provFromCode (eqc
      (substfcT (tcFn a) (tcFn b) (tcFn (forallc f)))
      (substfcT (tcFn a) (tcFn b) (unT 6 (tcFn f))))) :=
    prf_mp (pcc_congr_substfcT_arg3_code (tcFn a) (tcFn b) (tcFn (forallc f)) (unT 6 (tcFn f))
      (substtc_inv_tcFn a) (substtc_inv_tcFn b) (substtc_inv_tcFn (forallc f))) hdot
  exact pcc_eq_trans_code _ _ _
    (substtc_inv_substfcT (substtc_inv_tcFn a) (substtc_inv_tcFn b)
      (substtc_inv_tcFn (forallc f)))
    hcongr (pcc_substfc_forall_dot a b f)


/-! ## §6 · SONDAS DEL PASO 2 — especificacion de `pcc_eval_substfc` -/

/-- El codigo de la ecuacion interna (patron `evalNthcCode`, `Meta/EvalNthcPrf.lean:191`). -/
def evalSubstfcCode (v s f : Term) : Term :=
  eqCodeFn (substfcT (tcFn v) (tcFn s) (tcFn f)) (tcFn (substfc v s f))

theorem substTerm_evalSubstfcCode (k : Nat) (u v s f : Term) :
    substTerm k u (evalSubstfcCode v s f)
      = evalSubstfcCode (substTerm k u v) (substTerm k u s) (substTerm k u f) := by
  simp only [evalSubstfcCode, eqCodeFn, substfcT, funcc, tcFn, substfc, cons, nil, zero, succ,
    substTerm, substTerms, substTerm_numeral, substTerm_strCode]

theorem liftTerm_evalSubstfcCode (k : Nat) (v s f : Term) :
    liftTerm k (evalSubstfcCode v s f)
      = evalSubstfcCode (liftTerm k v) (liftTerm k s) (liftTerm k f) := by
  simp only [evalSubstfcCode, eqCodeFn, substfcT, funcc, tcFn, substfc, cons, nil, zero, succ,
    liftTerm, liftTerms, liftTerm_numeral, liftTerm_strCode]

/-- CONTROL NEGATIVO: el enunciado NO es una reflexividad disfrazada. -/
example (v s f : Term) : True := by
  fail_if_success
    exact (rfl : substfcT (tcFn v) (tcFn s) (tcFn f) = tcFn (substfc v s f))
  trivial

/-- **EL PASO INDUCTIVO `∀` DE `pcc_eval_substfc`, CERRADO MODULO UNA SOLA PIEZA.**

    `hIH`   = hipotesis de induccion sobre el subcodigo `f`, con `v`/`s` cuantificados dentro.
    `hLift` = **`pcc_dot_liftc`**. **NO EXISTE** en produccion (grep: 0 ocurrencias de
              `pcc_dot_liftc` / `pcc_eval_liftc`).

    Todo lo demas sale de produccion + §1-§5. Es la MEDIDA exacta del hueco: el caso `∀`
    (y su gemelo `∃`) se reduce a `pcc_dot_liftc` y a nada mas. -/
theorem paso2_caso_forall (v s f : Term)
    (hIH : Prf (provFromCode (evalSubstfcCode (succ v) (liftc zero s) f)))
    (hLift : Prf (provFromCode (eqc (liftcT (termCode zero) (tcFn s)) (tcFn (liftc zero s))))) :
    Prf (provFromCode (evalSubstfcCode v s (forallc f))) := by
  unfold evalSubstfcCode at hIH ⊢
  have iz : ∀ W, Prf (substtc zero W (termCode zero) =eq termCode zero) :=
    fun W => prf_substtc_termCode_zero 0 W
  have iL : ∀ W, Prf (substtc zero W (liftcT (termCode zero) (tcFn s))
      =eq liftcT (termCode zero) (tcFn s)) := substtc_inv_liftcT iz (substtc_inv_tcFn s)
  have iA : ∀ W, Prf (substtc zero W (substfcT (tcFn v) (tcFn s) (tcFn (forallc f)))
      =eq substfcT (tcFn v) (tcFn s) (tcFn (forallc f))) :=
    substtc_inv_substfcT (substtc_inv_tcFn v) (substtc_inv_tcFn s) (substtc_inv_tcFn (forallc f))
  -- (1) fuego (a)+(b): la instancia interna del axioma, ya dotada
  have h1 : Prf (provFromCode (eqc (substfcT (tcFn v) (tcFn s) (tcFn (forallc f)))
      (unT 6 (substfcT (succcT (tcFn v)) (liftcT (termCode zero) (tcFn s)) (tcFn f))))) :=
    fuego_ab v s f
  -- (2) `succcT v̇ ↦ (σv)˙` : ecuacion de CODIGO, GRATIS (`prf_tc_succ'`)
  have h2 : Prf (provFromCode (eqc (substfcT (tcFn v) (tcFn s) (tcFn (forallc f)))
      (unT 6 (substfcT (tcFn (succ v)) (liftcT (termCode zero) (tcFn s)) (tcFn f))))) :=
    prf_mp (prf_provCode_congr (prf_congr_eqCodeFn (prf_refl _)
      (prf_congr_unT (prf_congr_substfcT (prf_eq_symm (prf_tc_succ' v))
        (prf_refl _) (prf_refl _))))) h1
  -- (3) `liftcT ⌜0⌝ ṡ ↦ (liftc 0 s)˙` : INTERNO — aqui entra `hLift`
  have h3 : Prf (provFromCode (eqc
      (unT 6 (substfcT (tcFn (succ v)) (liftcT (termCode zero) (tcFn s)) (tcFn f)))
      (unT 6 (substfcT (tcFn (succ v)) (tcFn (liftc zero s)) (tcFn f))))) :=
    prf_mp (pcc_congr_unT_code 6 _ _
      (substtc_inv_substfcT (substtc_inv_tcFn (succ v)) iL (substtc_inv_tcFn f)))
      (prf_mp (pcc_congr_substfcT_arg2_code (tcFn (succ v)) (tcFn f)
        (liftcT (termCode zero) (tcFn s)) (tcFn (liftc zero s))
        (substtc_inv_tcFn (succ v)) (substtc_inv_tcFn f) iL) hLift)
  -- (4) la HI, bajo el `unT 6`
  have h4 : Prf (provFromCode (eqc
      (unT 6 (substfcT (tcFn (succ v)) (tcFn (liftc zero s)) (tcFn f)))
      (unT 6 (tcFn (substfc (succ v) (liftc zero s) f))))) :=
    prf_mp (pcc_congr_unT_code 6 _ _
      (substtc_inv_substfcT (substtc_inv_tcFn (succ v)) (substtc_inv_tcFn (liftc zero s))
        (substtc_inv_tcFn f))) hIH
  -- (5) el KIT pliega el `unT 6` en el punto de `forallc`
  have h5 : Prf (provFromCode (eqc (unT 6 (tcFn (substfc (succ v) (liftc zero s) f)))
      (tcFn (forallc (substfc (succ v) (liftc zero s) f))))) :=
    pcc_dot_un 6 (substfc (succ v) (liftc zero s) f)
  -- (6) la ecuacion OBJETO del axioma, dotada GRATIS por `prf_congr_tcFn`
  have h6 : Prf (provFromCode (eqc (tcFn (forallc (substfc (succ v) (liftc zero s) f)))
      (tcFn (substfc v s (forallc f))))) :=
    prf_mp (prf_provCode_congr (prf_congr_eqCodeFn (prf_refl _)
      (prf_congr_tcFn (prf_eq_symm (prf_substfc_forall v s f)))))
      (prf_provFromCode_eqCodeFn_refl (tcFn (forallc (substfc (succ v) (liftc zero s) f))))
  -- (7) cadena
  exact pcc_eq_trans_code _ _ _ iA h2
    (pcc_eq_trans_code _ _ _
      (substtc_inv_unT (substtc_inv_substfcT (substtc_inv_tcFn (succ v)) iL
        (substtc_inv_tcFn f)))
      h3
      (pcc_eq_trans_code _ _ _
        (substtc_inv_unT (substtc_inv_substfcT (substtc_inv_tcFn (succ v))
          (substtc_inv_tcFn (liftc zero s)) (substtc_inv_tcFn f)))
        h4
        (pcc_eq_trans_code _ _ _
          (substtc_inv_unT (substtc_inv_tcFn (substfc (succ v) (liftc zero s) f)))
          h5 h6)))

end Paso2

#print axioms Paso2.substTerm_evalSubstfcCode
#print axioms Paso2.liftTerm_evalSubstfcCode
#print axioms Paso2.paso2_caso_forall


namespace Paso2Desc

open ROBINSON_PlusPlus.Meta.CantorMonoPrf ROBINSON_PlusPlus.Meta.NatOrderPrf
open ROBINSON_PlusPlus.Meta.ChainPrf

/-! ## §7 · EL DESCENSO — de la forma ECUACIONAL sale `hijo < padre` por CANTOR.

Copias literales de `sondeos/DiscriminaEcuacional.lean:3371,3374`. -/

def shapeNul (X : Term) (k : Nat) : Formula := Formula.eq X (cons (numeralM k) nil)
def shapeUn (X : Term) (k : Nat) : Formula :=
  Formula.eq X (cons (numeralM k) (cons (nthc X (numeralM 1)) nil))
def shapeBin (X : Term) (k : Nat) : Formula :=
  Formula.eq X (cons (numeralM k)
    (cons (nthc X (numeralM 1)) (cons (nthc X (numeralM 2)) nil)))

/-! ### Los tags ecuacionales SON los constructores de codigo de formula, por `rfl` -/

theorem shapeNul2_es_botc (X : Term) : shapeNul X 2 = Formula.eq X botc := rfl
theorem shapeBin4_es_eqc (X : Term) :
    shapeBin X 4 = Formula.eq X (eqc (nthc X (numeralM 1)) (nthc X (numeralM 2))) := rfl
theorem shapeBin5_es_implc (X : Term) :
    shapeBin X 5 = Formula.eq X (implc (nthc X (numeralM 1)) (nthc X (numeralM 2))) := rfl
theorem shapeUn6_es_forallc (X : Term) :
    shapeUn X 6 = Formula.eq X (forallc (nthc X (numeralM 1))) := rfl
theorem shapeUn9_es_exc (X : Term) :
    shapeUn X 9 = Formula.eq X (exc (nthc X (numeralM 1))) := rfl

/-! ### El descenso, con `prf_cantor_mono_left/right` + `prf_lt_trans`. CERO piezas nuevas. -/

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

/-! ## §8 · La ECUACION OBJETO del caso `∀`, disparada por la forma ecuacional -/

/-- De `X ≐ forallc a` sale la ecuacion de recursion del axioma, a nivel OBJETO. GRATIS. -/
theorem ec_objeto_forall (v s X a : Term) (hX : Prf (X =eq forallc a)) :
    Prf (substfc v s X =eq forallc (substfc (succ v) (liftc zero s) a)) :=
  prf_eq_trans (prf_congr_substfc_arg3 hX) (prf_substfc_forall v s a)

/-- Idem para `implc`: **sin `liftc`**, luego este caso NO tiene el hueco del `∀`. -/
theorem ec_objeto_impl (v s X a b : Term) (hX : Prf (X =eq implc a b)) :
    Prf (substfc v s X =eq implc (substfc v s a) (substfc v s b)) :=
  prf_eq_trans (prf_congr_substfc_arg3 hX) (prf_substfc_impl v s a b)

/-- Y para `eqc`: el `substfc` recurre a **`substtc`** ⇒ el teorema es MUTUO. -/
theorem ec_objeto_eq (v s X a b : Term) (hX : Prf (X =eq eqc a b)) :
    Prf (substfc v s X =eq eqc (substtc v s a) (substtc v s b)) :=
  prf_eq_trans (prf_congr_substfc_arg3 hX) (prf_substfc_eq v s a b)

end Paso2Desc

#print axioms Paso2Desc.shapeUn6_es_forallc
#print axioms Paso2Desc.descenso_un
#print axioms Paso2Desc.descenso_bin1
#print axioms Paso2Desc.descenso_bin2
#print axioms Paso2Desc.ec_objeto_forall
#print axioms Paso2Desc.ec_objeto_impl
#print axioms Paso2Desc.ec_objeto_eq


namespace Paso2Ind

open Paso2
open ROBINSON_PlusPlus.Meta.StrongInductionPrf

/-! ## §9 · ¿ADMITE `prf_strong_induction` el predicado de `pcc_eval_substfc`?

`prf_strong_induction (Φ) (hΦ : liftFormula 1 Φ = Φ) (step) : ∀ t, Prf (substFormula 0 t Φ)`.
El gate REAL es `hΦ`: `Φ` no puede tener libre nada por encima del indice de induccion.
Con `v`/`s` cuantificados DENTRO (que es lo que dice `StrongInductionPrf.lean:170`), se cumple. -/

/-- El predicado: `#0` es el CODIGO sobre el que se induce; `v` (`#1`) y `s` (`#0`) van dentro. -/
def PHI : Formula :=
  Formula.forall (Formula.forall (provFromCode (evalSubstfcCode (.var 1) (.var 0) (.var 2))))

/-- **`hΦ` SE CUMPLE**: el predicado con `v`/`s` internos es admisible para `prf_strong_induction`. -/
theorem PHI_lift : liftFormula 1 PHI = PHI := by
  simp only [PHI, liftFormula, liftFormula_provFromCode_open, liftTerm_evalSubstfcCode,
    liftTerm, Nat.reduceLT, Nat.reduceAdd, reduceIte, if_true]

/-- Y la instancia en un codigo `t` es la ecuacion que queremos, con `∀v∀s` delante. -/
theorem PHI_at (t : Term) :
    substFormula 0 t PHI
      = Formula.forall (Formula.forall
          (provFromCode (evalSubstfcCode (.var 1) (.var 0) (liftTerm 0 (liftTerm 0 t))))) := by
  simp only [PHI, substFormula, substFormula_provFromCode_open, substTerm_evalSubstfcCode,
    substTerm, substTerms, liftTerm, liftTerms, Nat.reduceLT, Nat.reduceAdd, Nat.reduceEqDiff,
    Nat.reduceSub, Nat.reduceGT, reduceIte, if_true]

end Paso2Ind

#print axioms Paso2Ind.PHI_lift
#print axioms Paso2Ind.PHI_at


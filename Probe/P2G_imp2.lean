/- # `Probe/P2G_imp2.lean` — ESTRATEGIA (B): internalizar del todo la transitividad.

   Objetivo: reescribir el paso inductivo del caso `∀` de `pcc_eval_substfc` en forma
   `PrfH Γ` con la guarda `hasWit s` en Γ, de modo que las dos hipótesis que hoy cuelgan
   (`hLift` y la guarda de la HI) se descarguen solas.

   Pieza nueva de la estrategia (B):
     `pcc_eq_trans_code_imp2 (X Y Z) (hX) : Prf (⌜X=Y⌝̇ ⇒ ⌜Y=Z⌝̇ ⇒ ⌜X=Z⌝̇)`
   — los DOS eslabones internalizados. Con ella la cadena entera se monta bajo `PrfH Γ`
   por puros `PrfH.mp` + `prf_to_prfH`.

   ⚠️ CERO axiomas de Lean nuevos, cero `sorry`. `substfcT`/`liftcT`/… son DEFINICIONES:
   ninguna ecuación de recursión suya se postula.

   §0-§6 son copia LITERAL de `sondeos/Paso2CasoForall.lean:36-495` (el fichero debe ser
   autocontenido: no se puede importar `sondeos/`).
   §7 es la pieza nueva. §8-§9 copian `hasWit` (`sondeos/ClausuraLiftSinWTs.lean:96-145,1389`)
   y `targetLift` (`sondeos/DescensoLiftc.lean:79`). §10 es el teorema diana. -/
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
open ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf

set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

namespace P2Gimp2

/-! ## §0 · Piezas GENÉRICAS (copia de `sondeos/Paso2CasoForall.lean:36-80`) -/

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

theorem prf_congr_funcc3 {sc x x' y y' z z' : Term}
    (hx : Prf (x =eq x')) (hy : Prf (y =eq y')) (hz : Prf (z =eq z')) :
    Prf (funcc sc (cons x (cons y (cons z nil)))
      =eq funcc sc (cons x' (cons y' (cons z' nil)))) :=
  prf_congr_funcc2 (prf_eq_trans (prf_congr_cons_head hx)
    (prf_congr_cons_tail (prf_eq_trans (prf_congr_cons_head hy)
      (prf_congr_cons_tail (prf_congr_cons_head hz)))))

/-! ## §1 · Los constructores de código (DEFINICIONES, sin ecuaciones postuladas) -/

def substfcT (v s f : Term) : Term :=
  funcc (strCode "substfc") (cons v (cons s (cons f nil)))
def liftcT (c t : Term) : Term := funcc (strCode "liftc") (cons c (cons t nil))

theorem prf_congr_substfcT {v v' s s' f f' : Term}
    (hv : Prf (v =eq v')) (hs : Prf (s =eq s')) (hf : Prf (f =eq f')) :
    Prf (substfcT v s f =eq substfcT v' s' f') := prf_congr_funcc3 hv hs hf
theorem prf_congr_liftcT {c c' t t' : Term} (hc : Prf (c =eq c')) (ht : Prf (t =eq t')) :
    Prf (liftcT c t =eq liftcT c' t') :=
  prf_congr_funcc2 (prf_eq_trans (prf_congr_cons_head hc)
    (prf_congr_cons_tail (prf_congr_cons_head ht)))

theorem prf_substtc_substfcT (v W x y z : Term) :
    Prf (substtc v W (substfcT x y z)
      =eq substfcT (substtc v W x) (substtc v W y) (substtc v W z)) :=
  prf_substtc_funcc3 v W (strCode "substfc") x y z
theorem prf_substtc_liftcT (v W x y : Term) :
    Prf (substtc v W (liftcT x y) =eq liftcT (substtc v W x) (substtc v W y)) :=
  prf_substtc_funcc2 v W (strCode "liftc") x y

theorem substtc_inv_substfcT {X Y Z : Term}
    (hX : ∀ W, Prf (substtc zero W X =eq X)) (hY : ∀ W, Prf (substtc zero W Y =eq Y))
    (hZ : ∀ W, Prf (substtc zero W Z =eq Z)) :
    ∀ W, Prf (substtc zero W (substfcT X Y Z) =eq substfcT X Y Z) := fun W =>
  prf_eq_trans (prf_substtc_substfcT zero W X Y Z) (prf_congr_substfcT (hX W) (hY W) (hZ W))
theorem substtc_inv_liftcT {X Y : Term}
    (hX : ∀ W, Prf (substtc zero W X =eq X)) (hY : ∀ W, Prf (substtc zero W Y =eq Y)) :
    ∀ W, Prf (substtc zero W (liftcT X Y) =eq liftcT X Y) := fun W =>
  prf_eq_trans (prf_substtc_liftcT zero W X Y) (prf_congr_liftcT (hX W) (hY W))

/-! ## §2 · Utilidades de NIVEL -/

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

/-! ## §3 · La instancia INTERNA de `ax_substfc_forall` -/

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

/-! ## §4 · Congruencias INTERNAS (dentro de `Prov`) -/

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

/-! ## §5 · FUEGO (a)+(b) -/

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

/-! ## §6 · La especificación del PASO 2 -/

def evalSubstfcCode (v s f : Term) : Term :=
  eqCodeFn (substfcT (tcFn v) (tcFn s) (tcFn f)) (tcFn (substfc v s f))

/-- CONTROL NEGATIVO: el enunciado NO es una reflexividad disfrazada. -/
example (v s f : Term) : True := by
  fail_if_success
    exact (rfl : substfcT (tcFn v) (tcFn s) (tcFn f) = tcFn (substfc v s f))
  trivial

/-- El teorema de referencia, con las DOS hipótesis colgando (copia literal de
    `sondeos/Paso2CasoForall.lean:505`). Se incluye sólo como testigo de que el kit
    copiado es el bueno; el teorema diana es §10. -/
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
  have h1 : Prf (provFromCode (eqc (substfcT (tcFn v) (tcFn s) (tcFn (forallc f)))
      (unT 6 (substfcT (succcT (tcFn v)) (liftcT (termCode zero) (tcFn s)) (tcFn f))))) :=
    fuego_ab v s f
  have h2 : Prf (provFromCode (eqc (substfcT (tcFn v) (tcFn s) (tcFn (forallc f)))
      (unT 6 (substfcT (tcFn (succ v)) (liftcT (termCode zero) (tcFn s)) (tcFn f))))) :=
    prf_mp (prf_provCode_congr (prf_congr_eqCodeFn (prf_refl _)
      (prf_congr_unT (prf_congr_substfcT (prf_eq_symm (prf_tc_succ' v))
        (prf_refl _) (prf_refl _))))) h1
  have h3 : Prf (provFromCode (eqc
      (unT 6 (substfcT (tcFn (succ v)) (liftcT (termCode zero) (tcFn s)) (tcFn f)))
      (unT 6 (substfcT (tcFn (succ v)) (tcFn (liftc zero s)) (tcFn f))))) :=
    prf_mp (pcc_congr_unT_code 6 _ _
      (substtc_inv_substfcT (substtc_inv_tcFn (succ v)) iL (substtc_inv_tcFn f)))
      (prf_mp (pcc_congr_substfcT_arg2_code (tcFn (succ v)) (tcFn f)
        (liftcT (termCode zero) (tcFn s)) (tcFn (liftc zero s))
        (substtc_inv_tcFn (succ v)) (substtc_inv_tcFn f) iL) hLift)
  have h4 : Prf (provFromCode (eqc
      (unT 6 (substfcT (tcFn (succ v)) (tcFn (liftc zero s)) (tcFn f)))
      (unT 6 (tcFn (substfc (succ v) (liftc zero s) f))))) :=
    prf_mp (pcc_congr_unT_code 6 _ _
      (substtc_inv_substfcT (substtc_inv_tcFn (succ v)) (substtc_inv_tcFn (liftc zero s))
        (substtc_inv_tcFn f))) hIH
  have h5 : Prf (provFromCode (eqc (unT 6 (tcFn (substfc (succ v) (liftc zero s) f)))
      (tcFn (forallc (substfc (succ v) (liftc zero s) f))))) :=
    pcc_dot_un 6 (substfc (succ v) (liftc zero s) f)
  have h6 : Prf (provFromCode (eqc (tcFn (forallc (substfc (succ v) (liftc zero s) f)))
      (tcFn (substfc v s (forallc f))))) :=
    prf_mp (prf_provCode_congr (prf_congr_eqCodeFn (prf_refl _)
      (prf_congr_tcFn (prf_eq_symm (prf_substfc_forall v s f)))))
      (prf_provFromCode_eqCodeFn_refl (tcFn (forallc (substfc (succ v) (liftc zero s) f))))
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

/-! ############################################################################
    ## §7 · LA PIEZA NUEVA — ESTRATEGIA (B): transitividad interna con los DOS
           eslabones internalizados.

    `pcc_eq_trans_code` (`Meta/EvalArithPrf.lean:238`) toma sus dos eslabones como `Prf`,
    y `pcc_eq_trans_code_imp` (`:309`) sólo internaliza el SEGUNDO. Bajo `PrfH Γ` los
    eslabones que dependen de la guarda ya no son `Prf`, así que hace falta la forma con
    los DOS antecedentes.

    La hipótesis de invariancia sigue siendo **una sola** y **sobre `X`**: el contexto
    Leibniz es `Ac := (X = v₀)` y `X` es lo único que queda fijo bajo la sustitución.
    NO hace falta invariancia sobre `Y` ni sobre `Z`.
    ############################################################################ -/

/-- Deducción en `PrfH` con contexto ARBITRARIO (envoltura de `deduction_aux`).
    `prf_deduction` sólo cubre `Γ = []`; para meter el SEGUNDO antecedente hace falta
    descargar sobre un contexto ya no vacío. -/
theorem prfH_deduction {Γ : List Formula} {A B : Formula} (h : PrfH (A :: Γ) B) :
    PrfH Γ (A ⇒ B) := deduction_aux h A Γ rfl

/-- **Transitividad interna de `=` sobre códigos, con los DOS eslabones internalizados.**

    `⊢ Prov(⌜X=Y⌝) ⇒ Prov(⌜Y=Z⌝) ⇒ Prov(⌜X=Z⌝)`.

    Misma prueba que `pcc_eq_trans_code` (contexto Leibniz `Ac := (X = v₀)`), pero montada
    en `PrfH [⌜Y=Z⌝, ⌜X=Y⌝]` y descargada con dos deducciones. -/
theorem pcc_eq_trans_code_imp2 (X Y Z : Term) (hX : ∀ W, Prf (substtc zero W X =eq X)) :
    Prf (provFromCode (eqc X Y) ⇒ (provFromCode (eqc Y Z) ⇒ provFromCode (eqc X Z))) := by
  let Ac : Term := eqc X (varc (numeral 0))
  have hcomp : ∀ t : Term, Prf (substfc zero t Ac =eq eqc X t) := fun t =>
    prf_eq_trans (prf_substfc_eq zero t X (varc (numeral 0)))
      (prf_congr_eqCodeFn (hX t) (prf_substtc_varc0 t))
  refine prf_deduction (prfH_deduction ?_)
  let G : List Formula := [provFromCode (eqc Y Z), provFromCode (eqc X Y)]
  have h1 : PrfH G (provFromCode (eqc X Y)) :=
    PrfH.hyp G _ (List.Mem.tail _ (List.Mem.head _))
  have h2 : PrfH G (provFromCode (eqc Y Z)) := PrfH.hyp G _ (List.Mem.head _)
  have hY : PrfH G (provFromCode (substfc zero Y Ac)) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_eq_symm (hcomp Y))) _) h1
  have hZ : PrfH G (provFromCode (substfc zero Z Ac)) := PrfH_leibniz_apply Ac Y Z h2 hY
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcomp Z)) _) hZ

/-- **HALLAZGO** (no estaba en el encargo): la premisa de la estrategia (B) —«hace falta
    `imp2` porque no hay lema Γ‑polimorfo»— es FALSA. `PrfH_eq_trans_code`
    (`Meta/EvalCarcNthcPrf.lean:66`) ya es Γ‑polimorfo y está en producción (usado en
    `CodeTreeReflect`, `InAxiomsCodePrf`, `LineWFEfqPrf`, …). Con él, `imp2` sale en tres
    líneas — y la cadena de §10 se puede montar igualmente sin pasar por `imp2`. -/
theorem pcc_eq_trans_code_imp2' (X Y Z : Term) (hX : ∀ W, Prf (substtc zero W X =eq X)) :
    Prf (provFromCode (eqc X Y) ⇒ (provFromCode (eqc Y Z) ⇒ provFromCode (eqc X Z))) :=
  prf_deduction (prfH_deduction
    (PrfH_eq_trans_code X Y Z hX
      (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))) (PrfH.hyp _ _ (List.Mem.head _))))

/-! ############################################################################
    ## §8 · `hasWit` — copia LITERAL de `sondeos/ClausuraLiftSinWTs.lean:96-145,1389`
    ############################################################################ -/

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

/-- «`c` TIENE testigo» — el testigo está CUANTIFICADO, no dado. -/
def hasWit (c : Term) : Formula := Formula.ex (isTC1 (.var 0) (liftTerm 0 c))

/-! ## §9 · `targetLift` — copia LITERAL de `sondeos/DescensoLiftc.lean:79` -/

def targetLift (s : Term) : Formula :=
  provFromCode (eqc (liftcT (termCode zero) (tcFn s)) (tcFn (liftc zero s)))

/-- CONTROL NEGATIVO: no es una reflexividad disfrazada. -/
example (s : Term) : True := by
  fail_if_success
    exact (rfl : liftcT (termCode zero) (tcFn s) = tcFn (liftc zero s))
  trivial

/-! ############################################################################
    ## §10 · EL TEOREMA DIANA — el paso `∀` con la GUARDA en el contexto.

    Las dos hipótesis que hoy cuelgan en `paso2_caso_forall` se descargan DENTRO de
    `PrfH [hasWit s]`:
      * `hLift` sale de `DESCENSO_hasWit s : Prf (hasWit s ⇒ targetLift s)`
        (`sondeos/DescensoLiftc.lean:1388`), y `targetLift s` ES literalmente el `hLift`
        que pedía `paso2_caso_forall`;
      * la guarda de la HI sale de `CRIT_hasWit_lift s : Prf (hasWit s ⇒ hasWit (liftc zero s))`
        (`sondeos/ClausuraLiftSinWTs.lean:1392`).

    ⚠️ AJUSTE DEL ENUNCIADO, y por qué: ambas piezas viven en `sondeos/`, que la regla 5
    prohíbe importar, y reprobarlas aquí sería copiar dos desarrollos de ~1400 líneas cada
    uno. Entran por tanto como HIPÓTESIS EXPLÍCITAS con su enunciado EXACTO. Instanciándolas
    con los dos teoremas ya probados, el enunciado colapsa LITERALMENTE al pedido.
    ############################################################################ -/

/-- Versión GENÉRICA: la guarda es una fórmula cualquiera. Deja ver que del guardián sólo
    se usan las dos implicaciones, y nada de la estructura de `hasWit`. -/
theorem paso2_caso_forall_guarded_gen (v s f : Term) (Gs Gls : Formula)
    (hDesc : Prf (Gs ⇒ targetLift s))
    (hCrit : Prf (Gs ⇒ Gls))
    (hIH : Prf (Gls ⇒ provFromCode (evalSubstfcCode (succ v) (liftc zero s) f))) :
    Prf (Gs ⇒ provFromCode (evalSubstfcCode v s (forallc f))) := by
  unfold evalSubstfcCode at hIH ⊢
  unfold targetLift at hDesc
  -- invariancias `substtc` (idénticas a las de `paso2_caso_forall`)
  have iz : ∀ W, Prf (substtc zero W (termCode zero) =eq termCode zero) :=
    fun W => prf_substtc_termCode_zero 0 W
  have iL : ∀ W, Prf (substtc zero W (liftcT (termCode zero) (tcFn s))
      =eq liftcT (termCode zero) (tcFn s)) := substtc_inv_liftcT iz (substtc_inv_tcFn s)
  have iA : ∀ W, Prf (substtc zero W (substfcT (tcFn v) (tcFn s) (tcFn (forallc f)))
      =eq substfcT (tcFn v) (tcFn s) (tcFn (forallc f))) :=
    substtc_inv_substfcT (substtc_inv_tcFn v) (substtc_inv_tcFn s) (substtc_inv_tcFn (forallc f))
  have iY0 : ∀ W, Prf (substtc zero W
      (unT 6 (substfcT (tcFn (succ v)) (liftcT (termCode zero) (tcFn s)) (tcFn f)))
      =eq unT 6 (substfcT (tcFn (succ v)) (liftcT (termCode zero) (tcFn s)) (tcFn f))) :=
    substtc_inv_unT (substtc_inv_substfcT (substtc_inv_tcFn (succ v)) iL (substtc_inv_tcFn f))
  have iY1 : ∀ W, Prf (substtc zero W
      (unT 6 (substfcT (tcFn (succ v)) (tcFn (liftc zero s)) (tcFn f)))
      =eq unT 6 (substfcT (tcFn (succ v)) (tcFn (liftc zero s)) (tcFn f))) :=
    substtc_inv_unT (substtc_inv_substfcT (substtc_inv_tcFn (succ v))
      (substtc_inv_tcFn (liftc zero s)) (substtc_inv_tcFn f))
  have iY2 : ∀ W, Prf (substtc zero W (unT 6 (tcFn (substfc (succ v) (liftc zero s) f)))
      =eq unT 6 (tcFn (substfc (succ v) (liftc zero s) f))) :=
    substtc_inv_unT (substtc_inv_tcFn (substfc (succ v) (liftc zero s) f))
  -- eslabones LIBRES (no dependen de la guarda): h2, h5, h6
  have h1 : Prf (provFromCode (eqc (substfcT (tcFn v) (tcFn s) (tcFn (forallc f)))
      (unT 6 (substfcT (succcT (tcFn v)) (liftcT (termCode zero) (tcFn s)) (tcFn f))))) :=
    fuego_ab v s f
  have h2 : Prf (provFromCode (eqc (substfcT (tcFn v) (tcFn s) (tcFn (forallc f)))
      (unT 6 (substfcT (tcFn (succ v)) (liftcT (termCode zero) (tcFn s)) (tcFn f))))) :=
    prf_mp (prf_provCode_congr (prf_congr_eqCodeFn (prf_refl _)
      (prf_congr_unT (prf_congr_substfcT (prf_eq_symm (prf_tc_succ' v))
        (prf_refl _) (prf_refl _))))) h1
  have h5 : Prf (provFromCode (eqc (unT 6 (tcFn (substfc (succ v) (liftc zero s) f)))
      (tcFn (forallc (substfc (succ v) (liftc zero s) f))))) :=
    pcc_dot_un 6 (substfc (succ v) (liftc zero s) f)
  have h6 : Prf (provFromCode (eqc (tcFn (forallc (substfc (succ v) (liftc zero s) f)))
      (tcFn (substfc v s (forallc f))))) :=
    prf_mp (prf_provCode_congr (prf_congr_eqCodeFn (prf_refl _)
      (prf_congr_tcFn (prf_eq_symm (prf_substfc_forall v s f)))))
      (prf_provFromCode_eqCodeFn_refl (tcFn (forallc (substfc (succ v) (liftc zero s) f))))
  -- el tramo final (h5·h6) es LIBRE: se cierra con `pcc_eq_trans_code` normal
  have h56 : Prf (provFromCode (eqc (unT 6 (tcFn (substfc (succ v) (liftc zero s) f)))
      (tcFn (substfc v s (forallc f))))) :=
    pcc_eq_trans_code _ _ _ iY2 h5 h6
  -- a partir de aquí, TODO bajo el contexto Γ = [Gs]
  refine prf_deduction ?_
  let G : List Formula := [Gs]
  have hguard : PrfH G Gs := prfH_hyp_self Gs
  -- (α) la guarda paga `hLift`
  have hLiftG : PrfH G (provFromCode (eqc (liftcT (termCode zero) (tcFn s))
      (tcFn (liftc zero s)))) :=
    PrfH.mp _ _ _ (prf_to_prfH hDesc G) hguard
  -- (β) la guarda paga la guarda de la HI, y con ella la HI
  have hIHG : PrfH G (provFromCode (eqCodeFn
      (substfcT (tcFn (succ v)) (tcFn (liftc zero s)) (tcFn f))
      (tcFn (substfc (succ v) (liftc zero s) f)))) :=
    PrfH.mp _ _ _ (prf_to_prfH hIH G) (PrfH.mp _ _ _ (prf_to_prfH hCrit G) hguard)
  -- (3) el eslabón que consumía `hLift`
  have h3G : PrfH G (provFromCode (eqc
      (unT 6 (substfcT (tcFn (succ v)) (liftcT (termCode zero) (tcFn s)) (tcFn f)))
      (unT 6 (substfcT (tcFn (succ v)) (tcFn (liftc zero s)) (tcFn f))))) :=
    PrfH.mp _ _ _
      (prf_to_prfH (pcc_congr_unT_code 6 _ _
        (substtc_inv_substfcT (substtc_inv_tcFn (succ v)) iL (substtc_inv_tcFn f))) G)
      (PrfH.mp _ _ _
        (prf_to_prfH (pcc_congr_substfcT_arg2_code (tcFn (succ v)) (tcFn f)
          (liftcT (termCode zero) (tcFn s)) (tcFn (liftc zero s))
          (substtc_inv_tcFn (succ v)) (substtc_inv_tcFn f) iL) G)
        hLiftG)
  -- (4) el eslabón que consumía la HI
  have h4G : PrfH G (provFromCode (eqc
      (unT 6 (substfcT (tcFn (succ v)) (tcFn (liftc zero s)) (tcFn f)))
      (unT 6 (tcFn (substfc (succ v) (liftc zero s) f))))) :=
    PrfH.mp _ _ _
      (prf_to_prfH (pcc_congr_unT_code 6 _ _
        (substtc_inv_substfcT (substtc_inv_tcFn (succ v)) (substtc_inv_tcFn (liftc zero s))
          (substtc_inv_tcFn f))) G) hIHG
  -- (7) la cadena, ENTERA bajo `PrfH G`, con `pcc_eq_trans_code_imp2`
  have t46 : PrfH G (provFromCode (eqc
      (unT 6 (substfcT (tcFn (succ v)) (tcFn (liftc zero s)) (tcFn f)))
      (tcFn (substfc v s (forallc f))))) :=
    PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (pcc_eq_trans_code_imp2 _ _ _ iY1) G) h4G)
      (prf_to_prfH h56 G)
  have t36 : PrfH G (provFromCode (eqc
      (unT 6 (substfcT (tcFn (succ v)) (liftcT (termCode zero) (tcFn s)) (tcFn f)))
      (tcFn (substfc v s (forallc f))))) :=
    PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (pcc_eq_trans_code_imp2 _ _ _ iY0) G) h3G) t46
  exact PrfH.mp _ _ _
    (PrfH.mp _ _ _ (prf_to_prfH (pcc_eq_trans_code_imp2 _ _ _ iA) G) (prf_to_prfH h2 G)) t36

/-- **EL TEOREMA DIANA**, con `hasWit` literal. -/
theorem paso2_caso_forall_guarded (v s f : Term)
    (hDesc : Prf (hasWit s ⇒ targetLift s))
    (hCrit : Prf (hasWit s ⇒ hasWit (liftc zero s)))
    (hIH : Prf (hasWit (liftc zero s)
                 ⇒ provFromCode (evalSubstfcCode (succ v) (liftc zero s) f))) :
    Prf (hasWit s ⇒ provFromCode (evalSubstfcCode v s (forallc f))) :=
  paso2_caso_forall_guarded_gen v s f (hasWit s) (hasWit (liftc zero s)) hDesc hCrit hIH

/-! ### Control: el enunciado del diana coincide LITERALMENTE con el pedido
    (`Formula.impl` es la notación `⇒`). -/
example (v s f : Term)
    (hDesc : Prf (Formula.impl (hasWit s) (targetLift s)))
    (hCrit : Prf (Formula.impl (hasWit s) (hasWit (liftc zero s))))
    (hIH : Prf (Formula.impl (hasWit (liftc zero s))
                 (provFromCode (evalSubstfcCode (succ v) (liftc zero s) f)))) :
    Prf (Formula.impl (hasWit s) (provFromCode (evalSubstfcCode v s (forallc f)))) :=
  paso2_caso_forall_guarded v s f hDesc hCrit hIH

end P2Gimp2

#print axioms P2Gimp2.pcc_eq_trans_code_imp2
#print axioms P2Gimp2.pcc_eq_trans_code_imp2'
#print axioms P2Gimp2.prfH_deduction
#print axioms P2Gimp2.paso2_caso_forall
#print axioms P2Gimp2.paso2_caso_forall_guarded_gen
#print axioms P2Gimp2.paso2_caso_forall_guarded

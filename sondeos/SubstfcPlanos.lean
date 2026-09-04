/- # SF_planos — los CUATRO constructores PLANOS de `pcc_eval_substfc`.

   `bottom`, `impl`, `and`, `or`. Ninguno lleva `liftc` ⇒ ninguno necesita guarda, `hasWit`
   ni el DESCENSO. Base: `sondeos/Paso2CasoForall.lean` §0-§6 (kit copiado literalmente).

   Piezas NUEVAS respecto de aquel fichero:
     * `pcc_thm_inst4` / `pcc_axiom_inst4` — ⚠️ **YA ESTÁN EN PRODUCCIÓN** desde el 2026‑08‑31,
       promovidos DESDE ESTE MISMO SONDEO a `Meta/MpCodePrf.lean` (y exportados). NO volver a
       promoverlos: esta línea decía «no existían (sólo hasta `inst3`)» y llevaba obsoleta desde
       entonces — detectado por la auditoría de B3 (2026‑09‑04).
       `ax_substfc_impl/_and/_or` son `forall_4`.
     * `binK` + `prf_substtc_binK_at` — el constructor binario de código con la ETIQUETA
       ABSTRACTA (`termCode T`), que es lo que permite FACTORIZAR impl/and/or en UN lema.
     * `pcc_substfc_bin_dot` — la instancia interna del axioma, DOTADA, genérica en la etiqueta.
     * `paso2_caso_bin` — el ensamblaje, genérico en el tag `k : Nat`.

   ⚠️ CERO axiomas de Lean, cero `sorry`. `substfcT` es una DEFINICIÓN y nada más. -/
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
open ROBINSON_PlusPlus.Meta.Representability2Prf ROBINSON_PlusPlus.Meta.ForallElimCodePrf

set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

namespace SFPlanos

/-! ## §0 · Kit copiado de `sondeos/Paso2CasoForall.lean` §0-§1 (sólo lo que hace falta) -/

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

/-- El constructor de código `substfc` (DEFINICIÓN; ninguna ecuación suya se postula). -/
def substfcT (v s f : Term) : Term :=
  funcc (strCode "substfc") (cons v (cons s (cons f nil)))

theorem substfcT_termCode (v s f : Term) :
    substfcT (termCode v) (termCode s) (termCode f) = termCode (substfc v s f) := rfl

theorem prf_congr_substfcT {v v' s s' f f' : Term}
    (hv : Prf (v =eq v')) (hs : Prf (s =eq s')) (hf : Prf (f =eq f')) :
    Prf (substfcT v s f =eq substfcT v' s' f') := prf_congr_funcc3 hv hs hf

theorem prf_substtc_substfcT (v W x y z : Term) :
    Prf (substtc v W (substfcT x y z)
      =eq substfcT (substtc v W x) (substtc v W y) (substtc v W z)) :=
  prf_substtc_funcc3 v W (strCode "substfc") x y z

theorem substtc_inv_substfcT {X Y Z : Term}
    (hX : ∀ W, Prf (substtc zero W X =eq X)) (hY : ∀ W, Prf (substtc zero W Y =eq Y))
    (hZ : ∀ W, Prf (substtc zero W Z =eq Z)) :
    ∀ W, Prf (substtc zero W (substfcT X Y Z) =eq substfcT X Y Z) := fun W =>
  prf_eq_trans (prf_substtc_substfcT zero W X Y Z) (prf_congr_substfcT (hX W) (hY W) (hZ W))

theorem liftTerm_substfcT (k : Nat) (v s f : Term) :
    liftTerm k (substfcT v s f) = substfcT (liftTerm k v) (liftTerm k s) (liftTerm k f) := by
  simp only [substfcT, funcc, cons, nil, zero, succ, liftTerm, liftTerms, liftTerm_strCode]
theorem substTerm_substfcT (k : Nat) (u v s f : Term) :
    substTerm k u (substfcT v s f)
      = substfcT (substTerm k u v) (substTerm k u s) (substTerm k u f) := by
  simp only [substfcT, funcc, cons, nil, zero, succ, substTerm, substTerms, substTerm_strCode]

/-! ### Utilidades de NIVEL (`substtc` a nivel `numeral v` arbitrario) -/

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

/-! ## §1 · `binK` — el constructor BINARIO de código con la ETIQUETA ABSTRACTA.

Es `binT` con el tag dado como CÓDIGO (`H = termCode T`) en vez de como `Nat`. Esta es la
pieza que permite escribir **una sola vez** el caso binario y usarlo para `impl`, `and` y `or`:
el único punto donde el tag no reduce definicionalmente es la hoja `substCodeT n W T`, y ahí
entra `substCodeT_closed`. -/

def binK (H a b : Term) : Term := consT H (consT a (consT b (termCode nil)))

/-- Puente por `rfl` con el `binT` de producción. -/
theorem binK_binT (m : Nat) (a b : Term) : binK (termCode (numeralM m)) a b = binT m a b := rfl

theorem prf_congr_binK {H a a' b b' : Term} (ha : Prf (a =eq a')) (hb : Prf (b =eq b')) :
    Prf (binK H a b =eq binK H a' b') :=
  prf_congr_consT (prf_refl _) (prf_congr_consT ha (prf_congr_consT hb (prf_refl _)))

/-- `substtc` atraviesa `binK` a nivel ARBITRARIO (espeja `prf_substtc_binT`, que sólo vale
    a nivel `zero`). Requiere que el tag `T` sea CERRADO. -/
theorem prf_substtc_binK_at (T : Term) (hT : ∀ c : Nat, liftTerm c T = T)
    (n : Nat) (W a b : Term) :
    Prf (substtc (numeral n) W (binK (termCode T) a b)
      =eq binK (termCode T) (substtc (numeral n) W a) (substtc (numeral n) W b)) := by
  unfold binK consT
  refine prf_eq_trans (prf_substtc_funcc2 _ _ _ _ _) ?_
  refine prf_congr_funcc2 ?_
  refine prf_eq_trans (prf_congr_cons_head (prf_substtc_termCode_closed n W T hT)) ?_
  refine prf_congr_cons_tail (prf_congr_cons_head ?_)
  refine prf_eq_trans (prf_substtc_funcc2 _ _ _ _ _) ?_
  refine prf_congr_funcc2 ?_
  refine prf_congr_cons_tail (prf_congr_cons_head ?_)
  refine prf_eq_trans (prf_substtc_funcc2 _ _ _ _ _) ?_
  exact prf_congr_funcc2
    (prf_congr_cons_tail (prf_congr_cons_head (prf_substtc_termCode_zero n W)))

/-! ## §2 · `pcc_axiom_inst4` — la instanciación de un axioma `∀∀∀∀φ` codificado.

En producción sólo hay hasta `pcc_axiom_inst3` (`Meta/MpCodePrf.lean:243`), pero
`ax_substfc_impl/_and/_or` son **`forall_4`**. Un binder más, mismo patrón. -/

theorem pcc_thm_inst4 (φ : Formula) (h : Prf (forall_4 φ)) (w₁ w₂ w₃ w₄ : Term) :
    Prf (provFromCode (substfc zero w₄ (substfc (numeral 1) (liftc zero w₃)
      (substfc (numeral 2) (liftc zero (liftc zero w₂))
        (substfc (numeral 3) (liftc zero (liftc zero (liftc zero w₁))) (formCode φ)))))) := by
  have h0 : Prf (provFromCode (formCode (forall_4 φ))) := repr_pos'_prf h
  have h1 : Prf (provFromCode (substfc zero w₁ (formCode (forall_3 φ)))) :=
    prf_mp (pcc_forallElim_code_open (formCode (forall_3 φ)) w₁) h0
  have h2 : Prf (provFromCode (forallc (substfc (numeral 1) (liftc zero w₁)
      (formCode (forall_2 φ))))) :=
    prf_mp (prf_provCode_congr (prf_substfc_forall zero w₁ (formCode (forall_2 φ)))) h1
  have h3 : Prf (provFromCode (substfc zero w₂ (substfc (numeral 1) (liftc zero w₁)
      (formCode (forall_2 φ))))) :=
    prf_mp (pcc_forallElim_code_open _ w₂) h2
  have h4 : Prf (provFromCode (substfc zero w₂ (forallc (substfc (numeral 2)
      (liftc zero (liftc zero w₁)) (forallc (formCode φ)))))) :=
    prf_mp (prf_provCode_congr (prf_congr_substfc_arg3
      (prf_substfc_forall (numeral 1) (liftc zero w₁) (forallc (formCode φ))))) h3
  have h5 : Prf (provFromCode (forallc (substfc (numeral 1) (liftc zero w₂)
      (substfc (numeral 2) (liftc zero (liftc zero w₁)) (forallc (formCode φ)))))) :=
    prf_mp (prf_provCode_congr (prf_substfc_forall zero w₂
      (substfc (numeral 2) (liftc zero (liftc zero w₁)) (forallc (formCode φ))))) h4
  have h6 : Prf (provFromCode (substfc zero w₃ (substfc (numeral 1) (liftc zero w₂)
      (substfc (numeral 2) (liftc zero (liftc zero w₁)) (forallc (formCode φ)))))) :=
    prf_mp (pcc_forallElim_code_open _ w₃) h5
  have h7 : Prf (provFromCode (substfc zero w₃ (substfc (numeral 1) (liftc zero w₂)
      (forallc (substfc (numeral 3) (liftc zero (liftc zero (liftc zero w₁)))
        (formCode φ)))))) :=
    prf_mp (prf_provCode_congr (prf_congr_substfc_arg3 (prf_congr_substfc_arg3
      (prf_substfc_forall (numeral 2) (liftc zero (liftc zero w₁)) (formCode φ))))) h6
  have h8 : Prf (provFromCode (substfc zero w₃ (forallc (substfc (numeral 2)
      (liftc zero (liftc zero w₂))
      (substfc (numeral 3) (liftc zero (liftc zero (liftc zero w₁))) (formCode φ)))))) :=
    prf_mp (prf_provCode_congr (prf_congr_substfc_arg3
      (prf_substfc_forall (numeral 1) (liftc zero w₂)
        (substfc (numeral 3) (liftc zero (liftc zero (liftc zero w₁))) (formCode φ))))) h7
  have h9 : Prf (provFromCode (forallc (substfc (numeral 1) (liftc zero w₃)
      (substfc (numeral 2) (liftc zero (liftc zero w₂))
        (substfc (numeral 3) (liftc zero (liftc zero (liftc zero w₁))) (formCode φ)))))) :=
    prf_mp (prf_provCode_congr (prf_substfc_forall zero w₃
      (substfc (numeral 2) (liftc zero (liftc zero w₂))
        (substfc (numeral 3) (liftc zero (liftc zero (liftc zero w₁))) (formCode φ))))) h8
  exact prf_mp (pcc_forallElim_code_open _ w₄) h9

theorem pcc_axiom_inst4 (φ : Formula) (hmem : forall_4 φ ∈ axioms) (w₁ w₂ w₃ w₄ : Term) :
    Prf (provFromCode (substfc zero w₄ (substfc (numeral 1) (liftc zero w₃)
      (substfc (numeral 2) (liftc zero (liftc zero w₂))
        (substfc (numeral 3) (liftc zero (liftc zero (liftc zero w₁))) (formCode φ)))))) :=
  pcc_thm_inst4 φ (prf_ax hmem) w₁ w₂ w₃ w₄

/-! ## §3 · Congruencia INTERNA de `substfcT` en el 3er argumento (patrón §4 de `Paso2CasoForall`) -/

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

/-! ## §4 · El código de la ecuación interna (idéntico a `Paso2CasoForall` §6) -/

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

/-! ## §5 · CASO `bottom` — constructor NULARIO, axioma `forall_2`. El más barato de todos. -/

def AXBOT_BODY : Formula := substfc (.var 1) (.var 0) botc =eq botc

theorem AXBOT_BODY_ok : ax_substfc_bottom = forall_2 AXBOT_BODY := rfl

/-- La instancia INTERNA del axioma `ax_substfc_bottom`, DOTADA (patrón `pcc_substfc_forall_dot`). -/
theorem pcc_substfc_bottom_dot (v s : Term) :
    Prf (provFromCode (eqCodeFn (substfcT (tcFn v) (tcFn s) (nulT 2)) (nulT 2))) := by
  let W1 : Term := liftc zero (tcFn v)
  let W0 : Term := tcFn s
  have hin : Prf (substfc (numeral 1) W1 (formCode AXBOT_BODY)
      =eq eqCodeFn (substfcT W1 (varc (numeral 0)) (nulT 2)) (nulT 2)) :=
    prf_substfc_arith_open 1 W1 AXBOT_BODY
  have hA1 : Prf (W1 =eq tcFn v) := prf_liftc_tcFn v
  have hnorm : Prf (eqCodeFn (substfcT W1 (varc (numeral 0)) (nulT 2)) (nulT 2)
      =eq eqCodeFn (substfcT (tcFn v) (varc (numeral 0)) (nulT 2)) (nulT 2)) :=
    prf_congr_eqCodeFn (prf_congr_substfcT hA1 (prf_refl _) (prf_refl _)) (prf_refl _)
  have hout : Prf (substfc zero W0 (eqCodeFn (substfcT (tcFn v) (varc (numeral 0)) (nulT 2))
        (nulT 2))
      =eq eqCodeFn (substfcT (tcFn v) (tcFn s) (nulT 2)) (nulT 2)) := by
    refine prf_eq_trans (prf_substfc_eq zero W0 _ _) ?_
    refine prf_congr_eqCodeFn ?_ (prf_substtc_nulT 2 W0)
    refine prf_eq_trans (prf_substtc_substfcT zero W0 _ _ _) ?_
    exact prf_congr_substfcT (prf_substtc_tcFn W0 v) (prf_substtc_varc0 W0)
      (prf_substtc_nulT 2 W0)
  have hchain : Prf (substfc zero W0 (substfc (numeral 1) W1 (formCode AXBOT_BODY))
      =eq eqCodeFn (substfcT (tcFn v) (tcFn s) (nulT 2)) (nulT 2)) :=
    prf_eq_trans (prf_congr_substfc_arg3 (prf_eq_trans hin hnorm)) hout
  exact prf_mp (prf_provCode_congr hchain)
    (pcc_axiom_inst2 AXBOT_BODY (show ax_substfc_bottom ∈ axioms by simp [axioms])
      (tcFn v) (tcFn s))

/-- **CASO `bottom` DE `pcc_eval_substfc`, CERRADO.** Sin hipótesis: constructor nulario. -/
theorem paso2_caso_bottom (v s : Term) :
    Prf (provFromCode (evalSubstfcCode v s botc)) := by
  unfold evalSubstfcCode
  have iA : ∀ W, Prf (substtc zero W (substfcT (tcFn v) (tcFn s) (tcFn botc))
      =eq substfcT (tcFn v) (tcFn s) (tcFn botc)) :=
    substtc_inv_substfcT (substtc_inv_tcFn v) (substtc_inv_tcFn s) (substtc_inv_tcFn botc)
  have iB : ∀ W, Prf (substtc zero W (substfcT (tcFn v) (tcFn s) (nulT 2))
      =eq substfcT (tcFn v) (tcFn s) (nulT 2)) :=
    substtc_inv_substfcT (substtc_inv_tcFn v) (substtc_inv_tcFn s) (substtc_inv_nulT 2)
  -- (1) `tcFn botc ↦ nulT 2` bajo el 3er argumento de `substfcT`, DENTRO de `Prov`
  have h1 : Prf (provFromCode (eqc (substfcT (tcFn v) (tcFn s) (tcFn botc))
      (substfcT (tcFn v) (tcFn s) (nulT 2)))) :=
    prf_mp (pcc_congr_substfcT_arg3_code (tcFn v) (tcFn s) (tcFn botc) (nulT 2)
      (substtc_inv_tcFn v) (substtc_inv_tcFn s) (substtc_inv_tcFn botc)) (pcc_dot_nul_symm 2)
  -- (2) la instancia interna del axioma
  have h2 : Prf (provFromCode (eqc (substfcT (tcFn v) (tcFn s) (nulT 2)) (nulT 2))) :=
    pcc_substfc_bottom_dot v s
  -- (3) `nulT 2 ↦ tcFn botc` (el KIT, dirección directa)
  have h3 : Prf (provFromCode (eqc (nulT 2) (tcFn botc))) := pcc_dot_nul 2
  -- (4) la ecuación OBJETO del axioma, dotada GRATIS por `prf_congr_tcFn`
  have h4 : Prf (provFromCode (eqc (tcFn botc) (tcFn (substfc v s botc)))) :=
    prf_mp (prf_provCode_congr (prf_congr_eqCodeFn (prf_refl _)
      (prf_congr_tcFn (prf_eq_symm (prf_substfc_bottom v s)))))
      (prf_provFromCode_eqCodeFn_refl (tcFn botc))
  exact pcc_eq_trans_code _ _ _ iA h1
    (pcc_eq_trans_code _ _ _ iB h2
      (pcc_eq_trans_code _ _ _ (substtc_inv_nulT 2) h3 h4))

/-! ## §6 · CASO BINARIO — `impl`, `and`, `or` en UN SOLO lema.

Los tres axiomas son **literalmente la misma fórmula** salvo el tag (`5`, `7`, `8`), que en
el código es un `numeralM k` CERRADO. Se factoriza tomando el tag como un `Term` abstracto `T`
con la hipótesis de clausura `hT`; el único punto donde `T` bloquea la reducción definicional
es la hoja `substCodeT 3 W3 T`, y ahí basta `substCodeT_closed`. -/

def binct (T a b : Term) : Term := cons T (cons a (cons b nil))

theorem binct_implc (a b : Term) : binct (numeralM 5) a b = implc a b := rfl
theorem binct_andc (a b : Term) : binct (numeralM 7) a b = andc a b := rfl
theorem binct_orc (a b : Term) : binct (numeralM 8) a b = orc a b := rfl

def AXBIN_BODY (T : Term) : Formula :=
  substfc (.var 3) (.var 2) (binct T (.var 1) (.var 0))
    =eq binct T (substfc (.var 3) (.var 2) (.var 1)) (substfc (.var 3) (.var 2) (.var 0))

theorem AXBIN_impl : ax_substfc_impl = forall_4 (AXBIN_BODY (numeralM 5)) := rfl
theorem AXBIN_and : ax_substfc_and = forall_4 (AXBIN_BODY (numeralM 7)) := rfl
theorem AXBIN_or : ax_substfc_or = forall_4 (AXBIN_BODY (numeralM 8)) := rfl

/-- **La instancia INTERNA del axioma binario, DOTADA**, genérica en la etiqueta `T`.
    Un solo lema para `impl`, `and` y `or`. -/
theorem pcc_substfc_bin_dot (T : Term) (hT : ∀ c : Nat, liftTerm c T = T)
    (hmem : forall_4 (AXBIN_BODY T) ∈ axioms) (v s a b : Term) :
    Prf (provFromCode (eqCodeFn
      (substfcT (tcFn v) (tcFn s) (binK (termCode T) (tcFn a) (tcFn b)))
      (binK (termCode T) (substfcT (tcFn v) (tcFn s) (tcFn a))
        (substfcT (tcFn v) (tcFn s) (tcFn b))))) := by
  let W3 : Term := liftc zero (liftc zero (liftc zero (tcFn v)))
  let W2 : Term := liftc zero (liftc zero (tcFn s))
  let W1 : Term := liftc zero (tcFn a)
  let W0 : Term := tcFn b
  -- normalizaciones de los testigos levantados
  have hv3 : Prf (W3 =eq tcFn v) :=
    prf_eq_trans (prf_congr_liftc
      (prf_eq_trans (prf_congr_liftc (prf_liftc_tcFn v)) (prf_liftc_tcFn v)))
      (prf_liftc_tcFn v)
  have hs2 : Prf (W2 =eq tcFn s) :=
    prf_eq_trans (prf_congr_liftc (prf_liftc_tcFn s)) (prf_liftc_tcFn s)
  have ha1 : Prf (W1 =eq tcFn a) := prf_liftc_tcFn a
  -- (0) la instancia bruta, con la hoja del tag SIN evaluar
  have hkc : substCodeT 3 W3 T = termCode T := substCodeT_closed 3 W3 T hT
  have hin0 : Prf (substfc (numeral 3) W3 (formCode (AXBIN_BODY T))
      =eq eqCodeFn
        (substfcT W3 (varc (numeral 2))
          (binK (substCodeT 3 W3 T) (varc (numeral 1)) (varc (numeral 0))))
        (binK (substCodeT 3 W3 T) (substfcT W3 (varc (numeral 2)) (varc (numeral 1)))
          (substfcT W3 (varc (numeral 2)) (varc (numeral 0))))) :=
    prf_substfc_arith_open 3 W3 (AXBIN_BODY T)
  rw [hkc] at hin0
  -- (1) nivel 3 : `W3 ↦ v̇`
  have hnorm3 : Prf (eqCodeFn
        (substfcT W3 (varc (numeral 2))
          (binK (termCode T) (varc (numeral 1)) (varc (numeral 0))))
        (binK (termCode T) (substfcT W3 (varc (numeral 2)) (varc (numeral 1)))
          (substfcT W3 (varc (numeral 2)) (varc (numeral 0))))
      =eq eqCodeFn
        (substfcT (tcFn v) (varc (numeral 2))
          (binK (termCode T) (varc (numeral 1)) (varc (numeral 0))))
        (binK (termCode T) (substfcT (tcFn v) (varc (numeral 2)) (varc (numeral 1)))
          (substfcT (tcFn v) (varc (numeral 2)) (varc (numeral 0))))) :=
    prf_congr_eqCodeFn
      (prf_congr_substfcT hv3 (prf_refl _) (prf_refl _))
      (prf_congr_binK (prf_congr_substfcT hv3 (prf_refl _) (prf_refl _))
        (prf_congr_substfcT hv3 (prf_refl _) (prf_refl _)))
  -- (2) nivel 2 : `#2 ↦ ṡ`
  have k2v : Prf (substtc (numeral 2) W2 (tcFn v) =eq tcFn v) := prf_substtc_tcFn_at 2 W2 v
  have k2s : Prf (substtc (numeral 2) W2 (varc (numeral 2)) =eq tcFn s) :=
    prf_eq_trans (prf_mp (prf_substtc_var_eq (numeral 2) W2 (numeral 2)) (prf_refl _)) hs2
  have k21 : Prf (substtc (numeral 2) W2 (varc (numeral 1)) =eq varc (numeral 1)) :=
    prf_mp (prf_substtc_var_lt (numeral 2) W2 (numeral 1))
      (prf_gnum_lt (show (1 : Nat) < 2 by omega))
  have k20 : Prf (substtc (numeral 2) W2 (varc (numeral 0)) =eq varc (numeral 0)) :=
    prf_mp (prf_substtc_var_lt (numeral 2) W2 (numeral 0))
      (prf_gnum_lt (show (0 : Nat) < 2 by omega))
  have hmid2 : Prf (substfc (numeral 2) W2 (eqCodeFn
        (substfcT (tcFn v) (varc (numeral 2))
          (binK (termCode T) (varc (numeral 1)) (varc (numeral 0))))
        (binK (termCode T) (substfcT (tcFn v) (varc (numeral 2)) (varc (numeral 1)))
          (substfcT (tcFn v) (varc (numeral 2)) (varc (numeral 0)))))
      =eq eqCodeFn
        (substfcT (tcFn v) (tcFn s) (binK (termCode T) (varc (numeral 1)) (varc (numeral 0))))
        (binK (termCode T) (substfcT (tcFn v) (tcFn s) (varc (numeral 1)))
          (substfcT (tcFn v) (tcFn s) (varc (numeral 0))))) := by
    refine prf_eq_trans (prf_substfc_eq (numeral 2) W2 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_substfcT (numeral 2) W2 _ _ _) ?_
      refine prf_congr_substfcT k2v k2s ?_
      exact prf_eq_trans (prf_substtc_binK_at T hT 2 W2 _ _) (prf_congr_binK k21 k20)
    · refine prf_eq_trans (prf_substtc_binK_at T hT 2 W2 _ _) ?_
      refine prf_congr_binK ?_ ?_
      · exact prf_eq_trans (prf_substtc_substfcT (numeral 2) W2 _ _ _)
          (prf_congr_substfcT k2v k2s k21)
      · exact prf_eq_trans (prf_substtc_substfcT (numeral 2) W2 _ _ _)
          (prf_congr_substfcT k2v k2s k20)
  -- (3) nivel 1 : `#1 ↦ ȧ`
  have k1v : Prf (substtc (numeral 1) W1 (tcFn v) =eq tcFn v) := prf_substtc_tcFn_at 1 W1 v
  have k1s : Prf (substtc (numeral 1) W1 (tcFn s) =eq tcFn s) := prf_substtc_tcFn_at 1 W1 s
  have k1a : Prf (substtc (numeral 1) W1 (varc (numeral 1)) =eq tcFn a) :=
    prf_eq_trans (prf_mp (prf_substtc_var_eq (numeral 1) W1 (numeral 1)) (prf_refl _)) ha1
  have k10 : Prf (substtc (numeral 1) W1 (varc (numeral 0)) =eq varc (numeral 0)) :=
    prf_mp (prf_substtc_var_lt (numeral 1) W1 (numeral 0))
      (prf_gnum_lt (show (0 : Nat) < 1 by omega))
  have hmid1 : Prf (substfc (numeral 1) W1 (eqCodeFn
        (substfcT (tcFn v) (tcFn s) (binK (termCode T) (varc (numeral 1)) (varc (numeral 0))))
        (binK (termCode T) (substfcT (tcFn v) (tcFn s) (varc (numeral 1)))
          (substfcT (tcFn v) (tcFn s) (varc (numeral 0)))))
      =eq eqCodeFn
        (substfcT (tcFn v) (tcFn s) (binK (termCode T) (tcFn a) (varc (numeral 0))))
        (binK (termCode T) (substfcT (tcFn v) (tcFn s) (tcFn a))
          (substfcT (tcFn v) (tcFn s) (varc (numeral 0))))) := by
    refine prf_eq_trans (prf_substfc_eq (numeral 1) W1 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_substfcT (numeral 1) W1 _ _ _) ?_
      refine prf_congr_substfcT k1v k1s ?_
      exact prf_eq_trans (prf_substtc_binK_at T hT 1 W1 _ _) (prf_congr_binK k1a k10)
    · refine prf_eq_trans (prf_substtc_binK_at T hT 1 W1 _ _) ?_
      refine prf_congr_binK ?_ ?_
      · exact prf_eq_trans (prf_substtc_substfcT (numeral 1) W1 _ _ _)
          (prf_congr_substfcT k1v k1s k1a)
      · exact prf_eq_trans (prf_substtc_substfcT (numeral 1) W1 _ _ _)
          (prf_congr_substfcT k1v k1s k10)
  -- (4) nivel 0 : `#0 ↦ ḃ`
  have k0v : Prf (substtc zero W0 (tcFn v) =eq tcFn v) := prf_substtc_tcFn W0 v
  have k0s : Prf (substtc zero W0 (tcFn s) =eq tcFn s) := prf_substtc_tcFn W0 s
  have k0a : Prf (substtc zero W0 (tcFn a) =eq tcFn a) := prf_substtc_tcFn W0 a
  have k0b : Prf (substtc zero W0 (varc (numeral 0)) =eq tcFn b) := prf_substtc_varc0 W0
  have hout : Prf (substfc zero W0 (eqCodeFn
        (substfcT (tcFn v) (tcFn s) (binK (termCode T) (tcFn a) (varc (numeral 0))))
        (binK (termCode T) (substfcT (tcFn v) (tcFn s) (tcFn a))
          (substfcT (tcFn v) (tcFn s) (varc (numeral 0)))))
      =eq eqCodeFn
        (substfcT (tcFn v) (tcFn s) (binK (termCode T) (tcFn a) (tcFn b)))
        (binK (termCode T) (substfcT (tcFn v) (tcFn s) (tcFn a))
          (substfcT (tcFn v) (tcFn s) (tcFn b)))) := by
    refine prf_eq_trans (prf_substfc_eq zero W0 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_substfcT zero W0 _ _ _) ?_
      refine prf_congr_substfcT k0v k0s ?_
      exact prf_eq_trans (prf_substtc_binK_at T hT 0 W0 _ _) (prf_congr_binK k0a k0b)
    · refine prf_eq_trans (prf_substtc_binK_at T hT 0 W0 _ _) ?_
      refine prf_congr_binK ?_ ?_
      · exact prf_eq_trans (prf_substtc_substfcT zero W0 _ _ _)
          (prf_congr_substfcT k0v k0s k0a)
      · exact prf_eq_trans (prf_substtc_substfcT zero W0 _ _ _)
          (prf_congr_substfcT k0v k0s k0b)
  have hchain : Prf (substfc zero W0 (substfc (numeral 1) W1 (substfc (numeral 2) W2
        (substfc (numeral 3) W3 (formCode (AXBIN_BODY T)))))
      =eq eqCodeFn
        (substfcT (tcFn v) (tcFn s) (binK (termCode T) (tcFn a) (tcFn b)))
        (binK (termCode T) (substfcT (tcFn v) (tcFn s) (tcFn a))
          (substfcT (tcFn v) (tcFn s) (tcFn b)))) :=
    prf_eq_trans (prf_congr_substfc_arg3
      (prf_eq_trans (prf_congr_substfc_arg3
        (prf_eq_trans (prf_congr_substfc_arg3 (prf_eq_trans hin0 hnorm3)) hmid2)) hmid1)) hout
  exact prf_mp (prf_provCode_congr hchain)
    (pcc_axiom_inst4 (AXBIN_BODY T) hmem (tcFn v) (tcFn s) (tcFn a) (tcFn b))

/-! ### El ENSAMBLAJE binario, genérico en el tag `k : Nat` -/

/-- **El paso inductivo BINARIO de `pcc_eval_substfc`**, genérico en el tag.
    `hax`  = la instancia interna del axioma, dotada (§6).
    `hobj` = la ecuación OBJETO del axioma (uno de `prf_substfc_impl/_and/_or`). -/
theorem paso2_caso_bin (k : Nat) (v s a b : Term)
    (hax : Prf (provFromCode (eqCodeFn
      (substfcT (tcFn v) (tcFn s) (binT k (tcFn a) (tcFn b)))
      (binT k (substfcT (tcFn v) (tcFn s) (tcFn a)) (substfcT (tcFn v) (tcFn s) (tcFn b))))))
    (hobj : Prf (substfc v s (cons (numeralM k) (cons a (cons b nil)))
      =eq cons (numeralM k) (cons (substfc v s a) (cons (substfc v s b) nil))))
    (hA : Prf (provFromCode (evalSubstfcCode v s a)))
    (hB : Prf (provFromCode (evalSubstfcCode v s b))) :
    Prf (provFromCode (evalSubstfcCode v s (cons (numeralM k) (cons a (cons b nil))))) := by
  unfold evalSubstfcCode at hA hB ⊢
  let C : Term := cons (numeralM k) (cons a (cons b nil))
  have iSA : ∀ W, Prf (substtc zero W (substfcT (tcFn v) (tcFn s) (tcFn a))
      =eq substfcT (tcFn v) (tcFn s) (tcFn a)) :=
    substtc_inv_substfcT (substtc_inv_tcFn v) (substtc_inv_tcFn s) (substtc_inv_tcFn a)
  have iSB : ∀ W, Prf (substtc zero W (substfcT (tcFn v) (tcFn s) (tcFn b))
      =eq substfcT (tcFn v) (tcFn s) (tcFn b)) :=
    substtc_inv_substfcT (substtc_inv_tcFn v) (substtc_inv_tcFn s) (substtc_inv_tcFn b)
  have iX0 : ∀ W, Prf (substtc zero W (substfcT (tcFn v) (tcFn s) (tcFn C))
      =eq substfcT (tcFn v) (tcFn s) (tcFn C)) :=
    substtc_inv_substfcT (substtc_inv_tcFn v) (substtc_inv_tcFn s) (substtc_inv_tcFn C)
  have iX1 : ∀ W, Prf (substtc zero W (substfcT (tcFn v) (tcFn s) (binT k (tcFn a) (tcFn b)))
      =eq substfcT (tcFn v) (tcFn s) (binT k (tcFn a) (tcFn b))) :=
    substtc_inv_substfcT (substtc_inv_tcFn v) (substtc_inv_tcFn s)
      (substtc_inv_binT (substtc_inv_tcFn a) (substtc_inv_tcFn b))
  have iX2 : ∀ W, Prf (substtc zero W (binT k (substfcT (tcFn v) (tcFn s) (tcFn a))
        (substfcT (tcFn v) (tcFn s) (tcFn b)))
      =eq binT k (substfcT (tcFn v) (tcFn s) (tcFn a)) (substfcT (tcFn v) (tcFn s) (tcFn b))) :=
    substtc_inv_binT iSA iSB
  have iX3 : ∀ W, Prf (substtc zero W (binT k (tcFn (substfc v s a))
        (substfcT (tcFn v) (tcFn s) (tcFn b)))
      =eq binT k (tcFn (substfc v s a)) (substfcT (tcFn v) (tcFn s) (tcFn b))) :=
    substtc_inv_binT (substtc_inv_tcFn (substfc v s a)) iSB
  have iX4 : ∀ W, Prf (substtc zero W (binT k (tcFn (substfc v s a)) (tcFn (substfc v s b)))
      =eq binT k (tcFn (substfc v s a)) (tcFn (substfc v s b))) :=
    substtc_inv_binT (substtc_inv_tcFn (substfc v s a)) (substtc_inv_tcFn (substfc v s b))
  -- (1) `tcFn C ↦ binT k ȧ ḃ` bajo el 3er argumento de `substfcT`
  have h1 : Prf (provFromCode (eqc (substfcT (tcFn v) (tcFn s) (tcFn C))
      (substfcT (tcFn v) (tcFn s) (binT k (tcFn a) (tcFn b))))) :=
    prf_mp (pcc_congr_substfcT_arg3_code (tcFn v) (tcFn s) (tcFn C) (binT k (tcFn a) (tcFn b))
      (substtc_inv_tcFn v) (substtc_inv_tcFn s) (substtc_inv_tcFn C)) (pcc_dot_bin_symm k a b)
  -- (3) la HI sobre el PRIMER hijo, bajo `binT`
  have h3 : Prf (provFromCode (eqc
      (binT k (substfcT (tcFn v) (tcFn s) (tcFn a)) (substfcT (tcFn v) (tcFn s) (tcFn b)))
      (binT k (tcFn (substfc v s a)) (substfcT (tcFn v) (tcFn s) (tcFn b))))) :=
    prf_mp (pcc_congr_binT_1_code k (substfcT (tcFn v) (tcFn s) (tcFn b))
      (substfcT (tcFn v) (tcFn s) (tcFn a)) (tcFn (substfc v s a)) iSB iSA) hA
  -- (4) la HI sobre el SEGUNDO hijo, bajo `binT`
  have h4 : Prf (provFromCode (eqc
      (binT k (tcFn (substfc v s a)) (substfcT (tcFn v) (tcFn s) (tcFn b)))
      (binT k (tcFn (substfc v s a)) (tcFn (substfc v s b))))) :=
    prf_mp (pcc_congr_binT_2_code k (tcFn (substfc v s a))
      (substfcT (tcFn v) (tcFn s) (tcFn b)) (tcFn (substfc v s b))
      (substtc_inv_tcFn (substfc v s a)) iSB) hB
  -- (5) el KIT pliega el `binT` en el punto del constructor
  have h5 : Prf (provFromCode (eqc (binT k (tcFn (substfc v s a)) (tcFn (substfc v s b)))
      (tcFn (cons (numeralM k) (cons (substfc v s a) (cons (substfc v s b) nil)))))) :=
    pcc_dot_bin k (substfc v s a) (substfc v s b)
  -- (6) la ecuación OBJETO del axioma, dotada GRATIS por `prf_congr_tcFn`
  have h6 : Prf (provFromCode (eqc
      (tcFn (cons (numeralM k) (cons (substfc v s a) (cons (substfc v s b) nil))))
      (tcFn (substfc v s C)))) :=
    prf_mp (prf_provCode_congr (prf_congr_eqCodeFn (prf_refl _)
      (prf_congr_tcFn (prf_eq_symm hobj))))
      (prf_provFromCode_eqCodeFn_refl
        (tcFn (cons (numeralM k) (cons (substfc v s a) (cons (substfc v s b) nil)))))
  exact pcc_eq_trans_code _ _ _ iX0 h1
    (pcc_eq_trans_code _ _ _ iX1 hax
      (pcc_eq_trans_code _ _ _ iX2 h3
        (pcc_eq_trans_code _ _ _ iX3 h4
          (pcc_eq_trans_code _ _ _ iX4 h5 h6))))

/-! ### Las tres instancias -/

theorem paso2_caso_impl (v s a b : Term)
    (hA : Prf (provFromCode (evalSubstfcCode v s a)))
    (hB : Prf (provFromCode (evalSubstfcCode v s b))) :
    Prf (provFromCode (evalSubstfcCode v s (implc a b))) :=
  paso2_caso_bin 5 v s a b
    (pcc_substfc_bin_dot (numeralM 5) (fun c => liftTerm_numeralM c 5)
      (show ax_substfc_impl ∈ axioms by simp [axioms]) v s a b)
    (prf_substfc_impl v s a b) hA hB

theorem paso2_caso_and (v s a b : Term)
    (hA : Prf (provFromCode (evalSubstfcCode v s a)))
    (hB : Prf (provFromCode (evalSubstfcCode v s b))) :
    Prf (provFromCode (evalSubstfcCode v s (andc a b))) :=
  paso2_caso_bin 7 v s a b
    (pcc_substfc_bin_dot (numeralM 7) (fun c => liftTerm_numeralM c 7)
      (show ax_substfc_and ∈ axioms by simp [axioms]) v s a b)
    (prf_substfc_and v s a b) hA hB

theorem paso2_caso_or (v s a b : Term)
    (hA : Prf (provFromCode (evalSubstfcCode v s a)))
    (hB : Prf (provFromCode (evalSubstfcCode v s b))) :
    Prf (provFromCode (evalSubstfcCode v s (orc a b))) :=
  paso2_caso_bin 8 v s a b
    (pcc_substfc_bin_dot (numeralM 8) (fun c => liftTerm_numeralM c 8)
      (show ax_substfc_or ∈ axioms by simp [axioms]) v s a b)
    (prf_substfc_or v s a b) hA hB

/-! ### CONTROLES -/

set_option linter.unusedVariables false in
/-- CONTROL NEGATIVO: ninguno de los cuatro enunciados es una reflexividad disfrazada. -/
example (v s a b : Term) : True := by
  fail_if_success
    exact (rfl : substfcT (tcFn v) (tcFn s) (tcFn botc) = tcFn (substfc v s botc))
  fail_if_success
    exact (rfl : substfcT (tcFn v) (tcFn s) (tcFn (implc a b)) = tcFn (substfc v s (implc a b)))
  trivial

/-- CONTROL: los tres tags binarios son DISTINTOS (el lema genérico no los confunde). -/
example : binct (numeralM 5) zero zero ≠ binct (numeralM 7) zero zero := by
  intro h; exact absurd h (by decide)

end SFPlanos

#print axioms SFPlanos.pcc_axiom_inst4
#print axioms SFPlanos.pcc_substfc_bottom_dot
#print axioms SFPlanos.paso2_caso_bottom
#print axioms SFPlanos.pcc_substfc_bin_dot
#print axioms SFPlanos.paso2_caso_bin
#print axioms SFPlanos.paso2_caso_impl
#print axioms SFPlanos.paso2_caso_and
#print axioms SFPlanos.paso2_caso_or

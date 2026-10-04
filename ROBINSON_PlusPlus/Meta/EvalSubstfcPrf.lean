import ROBINSON_PlusPlus.Meta.EvalSubsttcPrf
import ROBINSON_PlusPlus.Meta.SubstfcCodePrf
import ROBINSON_PlusPlus.Meta.CodeWitnessPrf
import ROBINSON_PlusPlus.Meta.SubstfcWitnessPrf
import ROBINSON_PlusPlus.Meta.EvalLiftcPrf
import ROBINSON_PlusPlus.Meta.LiftcCodePrf
import ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf
import ROBINSON_PlusPlus.Meta.ForallElimCodePrf
import ROBINSON_PlusPlus.Meta.D3InDotPrf
import ROBINSON_PlusPlus.Meta.Delta0ReflectPrf
import ROBINSON_PlusPlus.Meta.PropCodePrf
import ROBINSON_PlusPlus.Meta.CantorMonoPrf
import ROBINSON_PlusPlus.Meta.InAxiomsCodePrf
/-!
# `Meta/EvalSubstfcPrf.lean` — **`pcc_eval_substfc`**: la evaluación PROVABLE de `substfc`

⭐ **El muro de `substfc`, en producción.** Con `v`, `s`, `f` **abstractos** y los testigos
como guarda:

    pcc_eval_substfc     (wF wT v s f) (hws : Prf (hasWit s)) (hfc : Prf (isFC1 wF wT f)) :
        Prf (provFromCode (eqc (substfcT (tcFn v) (tcFn s) (tcFn f)) (tcFn (substfc v s f))))
    pcc_eval_substfc_wit (v s f) : Prf (hasWit s ∧ hasWitF f ⇒ targetSubstfc v s f)

La segunda es la que consume el frente C3: su antecedente es **literalmente** el conjunto
extra que ADR‑020 metió dentro del `⇔` de los 7 esquemas, así que con ella el reflector
`hCarc` pasa a ser una MP (ver `Meta/LineWFGuardPrf.lean`).

## Cómo se prueba

Inducción fuerte de **UN SOLO SORT** sobre el código de fórmula. 🔑 **No hacen falta tres
sorts**: los tags 3 y 4 (`atomc`, `eqc`) descienden por `substtc`/`substtsc` —no por
`substfc`—, así que la inducción consume término y lista **como caja negra**, vía
`pcc_eval_substtc` / `pcc_eval_substtsc` (`Meta/EvalSubsttcPrf.lean`, B3.2). Ocho casos.

🔑 **El puente de testigos SE DISUELVE**: no se prueba, se **define**. El reconocedor
`isFormCodeE2` tiene las casillas de término apuntando a `wT` en la forma exacta que consume
`EvalSubsttcPrf`, así que la premisa sale por `rfl` (`bridge_isTC1`). El «gate» sale gratis
porque el paquete de testigos ya venía en un solo término.

## PROMOCIÓN B3.4 (2026‑09‑08) — 806 declaraciones, entran 90

`sondeos/EvalSubstfcPrf.lean` (8 421 l.) es la **acreción de cinco sondeos**: cuatro
namespaces que copiaban trabajo ya promovido (`SinWTs` = `CodeWitnessPrf`, `DescMutua` =
`LiftcCodePrf`+`EvalLiftcPrf`, `SFsubsttc` = **B3.2**, y la mayor parte de `Paso2`) más el
namespace `ENS`, que es el trabajo real. Medido:

* **697 de 806 declaraciones se BORRAN** — 576 duplicados exactos y cuatro namespaces enteros.
* El payload es `ENS` (81 declaraciones) **+ 9 piezas de `Paso2`** que `ENS` necesita de
  verdad (`unc`, `AXBODY`, `pcc_substfc_un_dot`, `fuego_ab_un`, `mem6`/`mem9`…).
* ⭐ **`ENS` sólo dependía de 41 nombres de los cuatro namespaces borrados, y 31 ya estaban
  en producción.** Es lo que hace que el borrado sea limpio.
* ⚠️ **Los 16 lemas `bridge_*` / `gO_*` / `gT_*` se DISUELVEN.** Existían para certificar por
  `rfl` que dos namespaces definían lo mismo —la trampa registrada de «misma definición en
  dos namespaces son DOS constantes»—. Tenían **cero usos**: eran certificados, no
  maquinaria. Al quedar una sola definición ya no dicen nada.
* ⛔ **`hPHI` era un duplicado FALSO de una clase nueva**: su *firma* coincide con la de
  `EvalLiftcPrf.hPHI` (`liftFormula 1 PHI = PHI`), pero la firma menciona `PHI`, que es un
  **homónimo** — dos constantes distintas. La regla «para un teorema basta comparar la firma»
  falla cuando la firma menciona un homónimo.
-/

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.Hilbert ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.TcArithPrf ROBINSON_PlusPlus.Meta.CheckArith
open ROBINSON_PlusPlus.Meta.Sigma1Prf ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
open ROBINSON_PlusPlus.Meta.MpCodePrf ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf
open ROBINSON_PlusPlus.Meta.NumCodeClosedPrf ROBINSON_PlusPlus.Meta.EvalArithPrf
open ROBINSON_PlusPlus.Meta.EvalListPrf ROBINSON_PlusPlus.Meta.EvalLtPrf
open ROBINSON_PlusPlus.Meta.EvalNthcPrf ROBINSON_PlusPlus.Meta.NatArithPrf
open ROBINSON_PlusPlus.Meta.DotConsPrf ROBINSON_PlusPlus.Meta.DerivCondPrf
open ROBINSON_PlusPlus.Meta.CodeCtorKit ROBINSON_PlusPlus.Meta.BdAllIntroPrf
open ROBINSON_PlusPlus.Meta.BoundedInPrf ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.ChainOkBoundedPrf ROBINSON_PlusPlus.Meta.TrackedCorePrf
open ROBINSON_PlusPlus.Meta.Sigma1CorePrf ROBINSON_PlusPlus.Meta.EvalBoundedPrf
open ROBINSON_PlusPlus.Meta.InAxiomsCodePrf ROBINSON_PlusPlus.Meta.Delta0ReflectPrf
open ROBINSON_PlusPlus.Meta.D3InDotPrf ROBINSON_PlusPlus.Meta.NumListPrf
open ROBINSON_PlusPlus.Meta.CantorMonoPrf ROBINSON_PlusPlus.Meta.StrongInductionPrf
open ROBINSON_PlusPlus.Meta.PropCodePrf ROBINSON_PlusPlus.Meta.NatMulPrf
open ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf ROBINSON_PlusPlus.Meta.EvalPredPrf
open ROBINSON_PlusPlus.Meta.LiftcCodePrf ROBINSON_PlusPlus.Meta.SubstfcCodePrf
open ROBINSON_PlusPlus.Meta.SubstfcWitnessPrf ROBINSON_PlusPlus.Meta.EvalSubsttcPrf
open ROBINSON_PlusPlus.Meta.ForallElimCodePrf ROBINSON_PlusPlus.Meta.SubstArith
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf.ENS

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

namespace ROBINSON_PlusPlus.Meta.EvalSubstfcPrf

/-! ############################################################################
    ## §0 · LAS NUEVE PIEZAS QUE SUBEN CON EL FRENTE (del namespace `Paso2` del sondeo)

    Del namespace `Paso2` (82 declaraciones) sólo hacían falta éstas: el constructor unario
    genérico en el tag `unc`, su cuerpo de axioma `AXBODY`, la instancia interna
    `pcc_substfc_un_dot`, la congruencia de la segunda ranura y las dos pertenencias
    `mem6`/`mem9`. Las otras 73 eran duplicados o exploración sin consumidor.
    ############################################################################ -/

theorem pcc_congr_substfcT_arg2_code (A C X Y : Term)
    (hA : ∀ W, Prf (substtc zero W A =eq A)) (hC : ∀ W, Prf (substtc zero W C =eq C))
    (hX : ∀ W, Prf (substtc zero W X =eq X))
    (hwA : Prf (hasWit A) := by hw_auto) (hwC : Prf (hasWit C) := by hw_auto)
    (hwX : Prf (hasWit X) := by hw_auto) (hwY : Prf (hasWit Y) := by hw_auto) :
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
    (PrfH_leibniz_apply Ac X Y (prfH_hyp_self _) (prf_to_prfH hAX _)
      (prf_hasWitF_eq2 (substfcT A X C) (substfcT A (varc (numeral 0)) C)
        (prf_hasWit_funcc3 (strCode "substfc") A X C hwA hwX hwC)
        (prf_hasWit_funcc3 (strCode "substfc") A (varc (numeral 0)) C hwA
          (prf_hasWit_varc (numeral 0)) hwC)) hwX hwY)

/-- Constructor UNARIO de codigo de FORMULA, parametrizado por el tag. -/
def unc (m : Nat) (a : Term) : Term := cons (numeralM m) (cons a nil)

/-- El cuerpo comun de `ax_substfc_forall` / `ax_substfc_ex`. -/
def AXBODY (m : Nat) : Formula :=
  substfc (.var 2) (.var 1) (unc m (.var 0))
    =eq unc m (substfc (succ (.var 2)) (liftc zero (.var 1)) (.var 0))

/-- LA UNICA pieza nueva de la abstraccion: con `m` abstracto, `substCodeT v w (numeralM m)`
    ya no reduce por `rfl` (con `m` literal si). Se cierra con `substCodeT_closed`. -/
theorem substCodeT_unc (v : Nat) (w : Term) (m : Nat) (a : Term) :
    substCodeT v w (unc m a) = unT m (substCodeT v w a) := by
  show consT (substCodeT v w (numeralM m)) (consT (substCodeT v w a) (termCode nil))
      = unT m (substCodeT v w a)
  rw [substCodeT_closed v w (numeralM m) (fun c => liftTerm_numeralM c m)]
  rfl

theorem substCodeF_AXBODY (m : Nat) (W : Term) :
    substCodeF 2 W (AXBODY m)
      = eqCodeFn
        (substfcT W (varc (numeral 1)) (unT m (varc (numeral 0))))
        (unT m (substfcT (succcT W) (liftcT (termCode zero) (varc (numeral 1)))
          (varc (numeral 0)))) := by
  show eqCodeFn (substCodeT 2 W (substfc (.var 2) (.var 1) (unc m (.var 0))))
      (substCodeT 2 W (unc m (substfc (succ (.var 2)) (liftc zero (.var 1)) (.var 0)))) = _
  rw [substCodeT_unc 2 W m (substfc (succ (.var 2)) (liftc zero (.var 1)) (.var 0))]
  show eqCodeFn (substfcT (substCodeT 2 W (.var 2)) (substCodeT 2 W (.var 1))
        (substCodeT 2 W (unc m (.var 0))))
      (unT m (substCodeT 2 W (substfc (succ (.var 2)) (liftc zero (.var 1)) (.var 0)))) = _
  rw [substCodeT_unc 2 W m (.var 0)]
  rfl

/-- **§3-GEN** — `pcc_substfc_forall_dot` con el tag ABSTRACTO. Copia estructural
    literal del caso `forall`: cambia `6` por `m` y `hin` pasa por `substCodeF_AXBODY`. -/
theorem pcc_substfc_un_dot (m : Nat) (hmem : forall_3 (AXBODY m) ∈ axioms) (a b f : Term) :
    Prf (provFromCode (eqCodeFn
      (substfcT (tcFn a) (tcFn b) (unT m (tcFn f)))
      (unT m (substfcT (succcT (tcFn a)) (liftcT (termCode zero) (tcFn b)) (tcFn f))))) := by
  let W2 : Term := liftc zero (liftc zero (tcFn a))
  let W1 : Term := liftc zero (tcFn b)
  let W0 : Term := tcFn f
  have hin : Prf (substfc (succ (succ zero)) W2 (formCode (AXBODY m))
      =eq eqCodeFn
        (substfcT W2 (varc (numeral 1)) (unT m (varc (numeral 0))))
        (unT m (substfcT (succcT W2) (liftcT (termCode zero) (varc (numeral 1)))
          (varc (numeral 0))))) := by
    have h := prf_substfc_arith_open 2 W2 (AXBODY m)
    rwa [substCodeF_AXBODY m W2] at h
  have hA2 : Prf (W2 =eq tcFn a) :=
    prf_eq_trans (ROBINSON_PlusPlus.Meta.NumCodeClosedPrf.prf_congr_liftc (prf_liftc_tcFn a)) (prf_liftc_tcFn a)
  have hnorm : Prf (eqCodeFn
        (substfcT W2 (varc (numeral 1)) (unT m (varc (numeral 0))))
        (unT m (substfcT (succcT W2) (liftcT (termCode zero) (varc (numeral 1)))
          (varc (numeral 0))))
      =eq eqCodeFn
        (substfcT (tcFn a) (varc (numeral 1)) (unT m (varc (numeral 0))))
        (unT m (substfcT (succcT (tcFn a)) (liftcT (termCode zero) (varc (numeral 1)))
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
        (substfcT (tcFn a) (varc (numeral 1)) (unT m (varc (numeral 0))))
        (unT m (substfcT (succcT (tcFn a)) (liftcT (termCode zero) (varc (numeral 1)))
          (varc (numeral 0)))))
      =eq eqCodeFn
        (substfcT (tcFn a) (tcFn b) (unT m (varc (numeral 0))))
        (unT m (substfcT (succcT (tcFn a)) (liftcT (termCode zero) (tcFn b))
          (varc (numeral 0))))) := by
    refine prf_eq_trans (prf_substfc_eq (succ zero) W1 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_substfcT (succ zero) W1 _ _ _) ?_
      refine prf_congr_substfcT ha1 hv1 ?_
      exact prf_eq_trans (prf_substtc_unT_at m 1 W1 (varc (numeral 0))) (prf_congr_unT hv0)
    · refine prf_eq_trans (prf_substtc_unT_at m 1 W1 _) ?_
      refine prf_congr_unT ?_
      refine prf_eq_trans (prf_substtc_substfcT (succ zero) W1 _ _ _) ?_
      refine prf_congr_substfcT ?_ ?_ hv0
      · exact prf_eq_trans (prf_substtc_succcT (succ zero) W1 (tcFn a)) (prf_congr_succcT ha1)
      · exact prf_eq_trans (prf_substtc_liftcT (succ zero) W1 _ _)
          (prf_congr_liftcT (prf_substtc_termCode_zero 1 W1) hv1)
  have hout : Prf (substfc zero W0 (eqCodeFn
        (substfcT (tcFn a) (tcFn b) (unT m (varc (numeral 0))))
        (unT m (substfcT (succcT (tcFn a)) (liftcT (termCode zero) (tcFn b))
          (varc (numeral 0)))))
      =eq eqCodeFn
        (substfcT (tcFn a) (tcFn b) (unT m (tcFn f)))
        (unT m (substfcT (succcT (tcFn a)) (liftcT (termCode zero) (tcFn b)) (tcFn f)))) := by
    refine prf_eq_trans (prf_substfc_eq zero W0 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_substfcT zero W0 _ _ _) ?_
      refine prf_congr_substfcT (prf_substtc_tcFn W0 a) (prf_substtc_tcFn W0 b) ?_
      exact prf_eq_trans (prf_substtc_unT_at m 0 W0 (varc (numeral 0)))
        (prf_congr_unT (prf_substtc_varc0 W0))
    · refine prf_eq_trans (prf_substtc_unT_at m 0 W0 _) ?_
      refine prf_congr_unT ?_
      refine prf_eq_trans (prf_substtc_substfcT zero W0 _ _ _) ?_
      refine prf_congr_substfcT ?_ ?_ (prf_substtc_varc0 W0)
      · exact prf_eq_trans (prf_substtc_succcT zero W0 (tcFn a))
          (prf_congr_succcT (prf_substtc_tcFn W0 a))
      · exact prf_eq_trans (prf_substtc_liftcT zero W0 _ _)
          (prf_congr_liftcT (prf_substtc_termCode_zero 0 W0) (prf_substtc_tcFn W0 b))
  have hchain : Prf (substfc zero W0 (substfc (succ zero) W1
      (substfc (succ (succ zero)) W2 (formCode (AXBODY m))))
      =eq eqCodeFn
        (substfcT (tcFn a) (tcFn b) (unT m (tcFn f)))
        (unT m (substfcT (succcT (tcFn a)) (liftcT (termCode zero) (tcFn b)) (tcFn f)))) :=
    prf_eq_trans (prf_congr_substfc_arg3
      (prf_eq_trans (prf_congr_substfc_arg3 (prf_eq_trans hin hnorm)) hmid)) hout
  exact prf_mp (prf_provCode_congr hchain)
    (pcc_axiom_inst3 (AXBODY m) hmem (tcFn a) (tcFn b) (tcFn f) (by hw_auto) (by hw_auto) (by hw_auto))

/-- **§5-GEN** — `fuego_ab` con el tag ABSTRACTO. -/
theorem fuego_ab_un (m : Nat) (hmem : forall_3 (AXBODY m) ∈ axioms) (a b f : Term) :
    Prf (provFromCode (eqCodeFn
      (substfcT (tcFn a) (tcFn b) (tcFn (unc m f)))
      (unT m (substfcT (succcT (tcFn a)) (liftcT (termCode zero) (tcFn b)) (tcFn f))))) := by
  have hdot : Prf (provFromCode (eqc (tcFn (unc m f)) (unT m (tcFn f)))) :=
    pcc_dot_un_symm m f
  have hcongr : Prf (provFromCode (eqc
      (substfcT (tcFn a) (tcFn b) (tcFn (unc m f)))
      (substfcT (tcFn a) (tcFn b) (unT m (tcFn f))))) :=
    prf_mp (pcc_congr_substfcT_arg3_code (tcFn a) (tcFn b) (tcFn (unc m f)) (unT m (tcFn f))
      (substtc_inv_tcFn a) (substtc_inv_tcFn b) (substtc_inv_tcFn (unc m f))) hdot
  exact pcc_eq_trans_code _ _ _
    (substtc_inv_substfcT (substtc_inv_tcFn a) (substtc_inv_tcFn b)
      (substtc_inv_tcFn (unc m f)))
    (by hw_auto) (by hw_auto) (by hw_auto)
    hcongr (pcc_substfc_un_dot m hmem a b f)

/-- Las dos pertenencias, discriminadas por `simp [axioms]`. -/
theorem mem6 : forall_3 (AXBODY 6) ∈ axioms := show ax_substfc_forall ∈ axioms by simp [axioms]

theorem mem9 : forall_3 (AXBODY 9) ∈ axioms := show ax_substfc_ex ∈ axioms by simp [axioms]

/-! ############################################################################
    ## §0 · Combinadores (copias literales de `sondeos/EvalSubsttc.lean` §D)
    ############################################################################ -/

/-! ############################################################################
    ## §1 · COPIAS LITERALES del reconocedor de codigo de TERMINO sin `wTs`
       (`sondeos/ClausuraLiftSinWTs.lean:109-145,1389`, identico al de
        `sondeos/EvalSubsttc.lean:1116-1140`, que es lo que consume `pcc_eval_substtc'`).
    ############################################################################ -/

/-! ### Fontaneria De Bruijn del bloque de TERMINO (copias literales) -/

/-! ############################################################################
    ## §2 · EL RECONOCEDOR DE CODIGO DE **FORMULA**, forma ECUACIONAL, con
       **DOS** listas testigo (`wF` formulas, `wT` terminos).

    Es la version ECUACIONAL de `isFormCodeB2` (`ClausuraLiftSinWTs.lean:1170`),
    exactamente como `isTermCodeE1` es la version ecuacional de `isTermCodeB1`.
    Ocho disyuntos ↔ ocho ecuaciones de `substfc`. Las casillas de TERMINO apuntan a `wT`
    (`In` para `eqc`, `argsIn` para `atomc`), que es LITERALMENTE lo que pide
    `pcc_eval_substtc'` / `pcc_eval_substtsc'` ⇒ **el puente no hace falta: es la
    definicion.**
    ############################################################################ -/

/-! ### Fontaneria De Bruijn del bloque de FORMULA -/

/-! ### Del testigo al NODO — espejo de `EvalSubsttc.prf_isTermCodeE1_of_In` -/

/-! ############################################################################
    ## §3 · EL OBJETIVO (copia literal de `sondeos/Paso2CasoForall.lean` §6)
    ############################################################################ -/

def targetSubstfc (v s X : Term) : Formula := provFromCode (evalSubstfcCode v s X)

theorem liftF_targetSubstfc (k : Nat) (v s X : Term) :
    liftFormula k (targetSubstfc v s X)
      = targetSubstfc (liftTerm k v) (liftTerm k s) (liftTerm k X) := by
  simp only [targetSubstfc, liftFormula_provFromCode_open, liftTerm_evalSubstfcCode]

theorem substF_targetSubstfc (k : Nat) (u v s X : Term) :
    substFormula k u (targetSubstfc v s X)
      = targetSubstfc (substTerm k u v) (substTerm k u s) (substTerm k u X) := by
  simp only [targetSubstfc, substFormula_provFromCode_open, substTerm_evalSubstfcCode]

theorem substF_hole_fc (v s u : Term) :
    substFormula 0 u (targetSubstfc (liftTerm 0 v) (liftTerm 0 s) (.var 0))
      = targetSubstfc v s u := by
  rw [substF_targetSubstfc]
  simp only [substTerm, FOL.substTerm_liftTerm, if_true]

theorem PrfH_congr_targetSubstfc {Γ : List Formula} {v s X X' : Term} (h : PrfH Γ (X =eq X'))
    (ha : PrfH Γ (targetSubstfc v s X)) : PrfH Γ (targetSubstfc v s X') :=
  (substF_hole_fc v s X') ▸
    PrfH_leibniz_subst (A := targetSubstfc (liftTerm 0 v) (liftTerm 0 s) (.var 0)) h
      ((substF_hole_fc v s X) ▸ ha)

/-! ############################################################################
    ## §4 · EL PREDICADO DE LA INDUCCION FUERTE.

    CUATRO binders INTERNOS (`wF`, `wT`, `v`, `s`) y la guarda DENTRO (es un `∃`
    interno via `hasWit`, luego NO anade binder exterior — leccion de
    `sondeos/GateGuardaEnriquecida.lean`). El codigo sobre el que se induce es `#4`.
    ############################################################################ -/

/-- La guarda completa: el sustituyendo tiene testigo de TERMINO y el codigo tiene
    testigo de FORMULA (que a su vez lleva su testigo de TERMINO). -/
def GUARD (wF wT s X : Term) : Formula := land (hasWit s) (isFC1 wF wT X)

def BODYsubstfc (wF wT v s X : Term) : Formula :=
  Formula.impl (GUARD wF wT s X) (targetSubstfc v s X)

theorem liftF_BODYsubstfc (k : Nat) (wF wT v s X : Term) :
    liftFormula k (BODYsubstfc wF wT v s X)
      = BODYsubstfc (liftTerm k wF) (liftTerm k wT) (liftTerm k v) (liftTerm k s) (liftTerm k X) := by
  simp only [BODYsubstfc, GUARD, land, liftFormula, liftF_hasWit, liftF_isFC1, liftF_targetSubstfc]

theorem substF_BODYsubstfc (k : Nat) (u wF wT v s X : Term) :
    substFormula k u (BODYsubstfc wF wT v s X)
      = BODYsubstfc (substTerm k u wF) (substTerm k u wT) (substTerm k u v) (substTerm k u s)
          (substTerm k u X) := by
  simp only [BODYsubstfc, GUARD, land, substFormula, substF_hasWit, substF_isFC1, substF_targetSubstfc]

/-- `#4` es el CODIGO; `#3` = `wF`, `#2` = `wT`, `#1` = `v`, `#0` = `s`. -/
def PHIsubstfcBody : Formula := BODYsubstfc (.var 3) (.var 2) (.var 1) (.var 0) (.var 4)

def PHIsubstfc : Formula :=
  Formula.forall (Formula.forall (Formula.forall (Formula.forall PHIsubstfcBody)))

/-- **EL GATE de `prf_strong_induction`.** -/
theorem hPHIsubstfc : liftFormula 1 PHIsubstfc = PHIsubstfc := by
  simp only [PHIsubstfc, PHIsubstfcBody, liftFormula, liftF_BODYsubstfc, liftTerm, Nat.reduceAdd, Nat.reduceLT,
    reduceIte]

/-! ### Instanciacion de los cuatro binders -/

theorem PHIsubstfc_at (t : Term) :
    substFormula 0 t PHIsubstfc
      = Formula.forall (Formula.forall (Formula.forall (Formula.forall
          (BODYsubstfc (.var 3) (.var 2) (.var 1) (.var 0)
            (liftTerm 0 (liftTerm 0 (liftTerm 0 (liftTerm 0 t)))))))) := by
  simp only [PHIsubstfc, PHIsubstfcBody, substFormula, substF_BODYsubstfc, substTerm, Nat.reduceAdd,
    Nat.reduceEqDiff, Nat.reduceGT, Nat.reduceSub, reduceIte, if_true]

theorem PHI_spec1 (t wF : Term) :
    substFormula 0 wF (Formula.forall (Formula.forall (Formula.forall
        (BODYsubstfc (.var 3) (.var 2) (.var 1) (.var 0)
          (liftTerm 0 (liftTerm 0 (liftTerm 0 (liftTerm 0 t))))))))
      = Formula.forall (Formula.forall (Formula.forall
          (BODYsubstfc (liftTerm 0 (liftTerm 0 (liftTerm 0 wF))) (.var 2) (.var 1) (.var 0)
            (liftTerm 0 (liftTerm 0 (liftTerm 0 t)))))) := by
  simp only [substFormula, substF_BODYsubstfc, substTerm, Nat.reduceAdd, Nat.reduceEqDiff,
    Nat.reduceGT, Nat.reduceSub, reduceIte, if_true, substTerm_liftLiftLiftLift]

theorem PHI_spec2 (t wF wT : Term) :
    substFormula 0 wT (Formula.forall (Formula.forall
        (BODYsubstfc (liftTerm 0 (liftTerm 0 (liftTerm 0 wF))) (.var 2) (.var 1) (.var 0)
          (liftTerm 0 (liftTerm 0 (liftTerm 0 t))))))
      = Formula.forall (Formula.forall
          (BODYsubstfc (liftTerm 0 (liftTerm 0 wF)) (liftTerm 0 (liftTerm 0 wT)) (.var 1) (.var 0)
            (liftTerm 0 (liftTerm 0 t)))) := by
  simp only [substFormula, substF_BODYsubstfc, substTerm, Nat.reduceAdd, Nat.reduceEqDiff,
    Nat.reduceGT, Nat.reduceSub, reduceIte, if_true, substTerm_liftLiftLift]

theorem PHI_spec3 (t wF wT v : Term) :
    substFormula 0 v (Formula.forall
        (BODYsubstfc (liftTerm 0 (liftTerm 0 wF)) (liftTerm 0 (liftTerm 0 wT)) (.var 1) (.var 0)
          (liftTerm 0 (liftTerm 0 t))))
      = Formula.forall
          (BODYsubstfc (liftTerm 0 wF) (liftTerm 0 wT) (liftTerm 0 v) (.var 0) (liftTerm 0 t)) := by
  simp only [substFormula, substF_BODYsubstfc, substTerm, Nat.reduceAdd, Nat.reduceEqDiff,
    Nat.reduceGT, Nat.reduceSub, reduceIte, if_true, FOL.substTerm_liftLift]

theorem PHI_spec4 (t wF wT v s : Term) :
    substFormula 0 s
        (BODYsubstfc (liftTerm 0 wF) (liftTerm 0 wT) (liftTerm 0 v) (.var 0) (liftTerm 0 t))
      = BODYsubstfc wF wT v s t := by
  simp only [substF_BODYsubstfc, substTerm, FOL.substTerm_liftTerm, if_true]

theorem PHIsubstfc_use {Γ : List Formula} (t wF wT v s : Term) (h : PrfH Γ (substFormula 0 t PHIsubstfc)) :
    PrfH Γ (BODYsubstfc wF wT v s t) := by
  rw [PHIsubstfc_at] at h
  have h1 := PrfH_spec h wF
  rw [PHI_spec1] at h1
  have h2 := PrfH_spec h1 wT
  rw [PHI_spec2] at h2
  have h3 := PrfH_spec h2 v
  rw [PHI_spec3] at h3
  have h4 := PrfH_spec h3 s
  rwa [PHI_spec4] at h4

/-! ### El `PSI` de la induccion fuerte, en la forma que se usa DENTRO del paso -/

def PSIat (X : Term) : Formula :=
  Formula.forall (Formula.impl (lt (.var 0) (liftTerm 0 X)) PHIsubstfc)

theorem PSIat_eq (X : Term) : substFormula 0 X (PSI PHIsubstfc) = PSIat X := psi_at PHIsubstfc X

theorem PSIat_inst {Γ : List Formula} {X : Term} (h : PrfH Γ (PSIat X)) (z : Term) :
    PrfH Γ (Formula.impl (lt z X) (substFormula 0 z PHIsubstfc)) := by
  have hi := PrfH_spec h z
  have e : substFormula 0 z (Formula.impl (lt (.var 0) (liftTerm 0 X)) PHIsubstfc)
      = Formula.impl (lt z X) (substFormula 0 z PHIsubstfc) := by
    simp only [substFormula, lt, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  rwa [e] at hi

/-- **La HIPOTESIS DE INDUCCION, ya instanciada**: si `z < X`, `z` tiene testigo de formula
    y `s'` testigo de termino, entonces vale el objetivo en `z` con `v'`/`s'` LIBRES. -/
theorem IH_at {Γ : List Formula} {X : Term} (hpsi : PrfH Γ (PSIat X)) (z : Term)
    (hlt : PrfH Γ (lt z X)) (wF wT v' s' : Term)
    (hguard : PrfH Γ (GUARD wF wT s' z)) : PrfH Γ (targetSubstfc v' s' z) :=
  PrfH.mp _ _ _ (PHIsubstfc_use z wF wT v' s' (PrfH.mp _ _ _ (PSIat_inst hpsi z) hlt)) hguard

/-! ############################################################################
    ## §5 · EL DESCENSO — copia literal de `sondeos/Paso2CasoForall.lean` §7
    ############################################################################ -/

theorem descenso_un (X : Term) (k : Nat) : Prf (shapeUn X k ⇒ lt (nthc X (numeralM 1)) X) := by
  refine prf_deduction ?_
  have h1 : Prf (lt (nthc X (numeralM 1)) (cons (nthc X (numeralM 1)) nil)) :=
    prf_cantor_mono_left _ _
  have h2 : Prf (lt (cons (nthc X (numeralM 1)) nil)
      (cons (numeralM k) (cons (nthc X (numeralM 1)) nil))) := prf_cantor_mono_right _ _
  have h3 : Prf (lt (nthc X (numeralM 1)) (cons (numeralM k) (cons (nthc X (numeralM 1)) nil))) :=
    prf_mp (prf_mp (prf_lt_trans _ _ _) h1) h2
  exact PrfH_lt_subst2
    (PrfH_eq_symm (prfH_hyp_self (shapeUn X k))) (prf_to_prfH h3 _)

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
  exact PrfH_lt_subst2
    (PrfH_eq_symm (prfH_hyp_self (shapeBin X k))) (prf_to_prfH h3 _)

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
  exact PrfH_lt_subst2
    (PrfH_eq_symm (prfH_hyp_self (shapeBin X k))) (prf_to_prfH h5 _)

/-! ############################################################################
    ## §6 · LOS OCHO CASOS, como HIPOTESIS con enunciado EXACTO.

    Cada uno es exactamente la forma en que el paso inductivo los consume.
    ############################################################################ -/

/-- tag 2 · `botc`. Cubierto por `sondeos/SubstfcPlanos.paso2_caso_bottom`. -/
def CasoBot : Prop := ∀ v s X : Term,
  Prf (Formula.impl (shapeNul X 2) (targetSubstfc v s X))

/-- tag 3 · `atomc`. Consume `pcc_eval_substtsc'` (lista de terminos). -/
def CasoAtom : Prop := ∀ wT v s X : Term,
  Prf (Formula.impl
    (land (wfAll1 wT) (land (shapeBin X 3) (argsIn wT (nthc X (numeralM 2)))))
    (targetSubstfc v s X))

/-- tag 4 · `eqc`. Consume `pcc_eval_substtc'` DOS veces. -/
def CasoEq : Prop := ∀ wT v s X : Term,
  Prf (Formula.impl
    (land (wfAll1 wT) (land (shapeBin X 4)
      (land (In (nthc X (numeralM 1)) wT) (In (nthc X (numeralM 2)) wT))))
    (targetSubstfc v s X))

/-- tags 5/7/8 · `implc`/`andc`/`orc`. Cubierto por `SubstfcPlanos.paso2_caso_bin`. -/
def CasoBin (k : Nat) : Prop := ∀ v s X : Term,
  Prf (Formula.impl
    (land (shapeBin X k)
      (land (targetSubstfc v s (nthc X (numeralM 1)))
            (targetSubstfc v s (nthc X (numeralM 2)))))
    (targetSubstfc v s X))

/-- tags 6/9 · `forallc`/`exc`. Cubierto por `Paso2Guardado.paso2_caso_forall_guarded`
    y `SubstfcEx.paso2_caso_ex_guarded`, **modulo reformular la HI de `Prf` a conjunto**. -/
def CasoUn (k : Nat) : Prop := ∀ v s X : Term,
  Prf (Formula.impl
    (land (hasWit s) (land (shapeUn X k)
      (targetSubstfc (succ v) (liftc zero s) (nthc X (numeralM 1)))))
    (targetSubstfc v s X))

/-- La clausura de la guarda bajo `liftc zero` — `CRIT_hasWit_lift`. -/
def HasWitLift : Prop := ∀ s : Term, Prf (Formula.impl (hasWit s) (hasWit (liftc zero s)))

/-! ############################################################################
    ## §7 · EL PASO INDUCTIVO — las OCHO ramas, cada una con contexto de DOS
       hipotesis (nunca cadenas de `List.Mem.tail`), y el or-elim al nivel `Prf`.
    ############################################################################ -/

/-- Todo lo que la rama necesita del contexto, empaquetado en UNA formula. -/
def CTXFsubstfc (wF wT s X : Term) : Formula :=
  land (land (PSIat X) (wfAll1 wT)) (land (hasWit s) (wfAllF wF wT))

section Ramas
variable (wF wT v s X : Term)

theorem rama_bot (hbot : CasoBot) :
    Prf (Formula.impl (clBot X) (Formula.impl (CTXFsubstfc wF wT s X) (targetSubstfc v s X))) := by
  refine prf_deduction (deduction_aux ?_ (CTXFsubstfc wF wT s X) [clBot X] rfl)
  exact PrfH.mp _ _ _ (prf_to_prfH (hbot v s X) _)
    (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))

theorem rama_atom (hatom : CasoAtom) :
    Prf (Formula.impl (clAtom wT X) (Formula.impl (CTXFsubstfc wF wT s X) (targetSubstfc v s X))) := by
  refine prf_deduction (deduction_aux ?_ (CTXFsubstfc wF wT s X) [clAtom wT X] rfl)
  have hcl : PrfH [CTXFsubstfc wF wT s X, clAtom wT X] (clAtom wT X) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hctx : PrfH [CTXFsubstfc wF wT s X, clAtom wT X] (CTXFsubstfc wF wT s X) :=
    PrfH.hyp _ _ (List.Mem.head _)
  have hwT : PrfH [CTXFsubstfc wF wT s X, clAtom wT X] (wfAll1 wT) :=
    PrfH_and_elim_right (PrfH_and_elim_left hctx)
  exact PrfH.mp _ _ _ (prf_to_prfH (hatom wT v s X) _) (PrfH_and_intro hwT hcl)

theorem rama_eq (heq : CasoEq) :
    Prf (Formula.impl (clEq wT X) (Formula.impl (CTXFsubstfc wF wT s X) (targetSubstfc v s X))) := by
  refine prf_deduction (deduction_aux ?_ (CTXFsubstfc wF wT s X) [clEq wT X] rfl)
  have hcl : PrfH [CTXFsubstfc wF wT s X, clEq wT X] (clEq wT X) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hctx : PrfH [CTXFsubstfc wF wT s X, clEq wT X] (CTXFsubstfc wF wT s X) :=
    PrfH.hyp _ _ (List.Mem.head _)
  have hwT : PrfH [CTXFsubstfc wF wT s X, clEq wT X] (wfAll1 wT) :=
    PrfH_and_elim_right (PrfH_and_elim_left hctx)
  exact PrfH.mp _ _ _ (prf_to_prfH (heq wT v s X) _) (PrfH_and_intro hwT hcl)

theorem rama_bin (k : Nat) (hbin : CasoBin k) :
    Prf (Formula.impl (clBin wF X k)
      (Formula.impl (CTXFsubstfc wF wT s X) (targetSubstfc v s X))) := by
  refine prf_deduction (deduction_aux ?_ (CTXFsubstfc wF wT s X) [clBin wF X k] rfl)
  have hcl : PrfH [CTXFsubstfc wF wT s X, clBin wF X k] (clBin wF X k) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hctx : PrfH [CTXFsubstfc wF wT s X, clBin wF X k] (CTXFsubstfc wF wT s X) :=
    PrfH.hyp _ _ (List.Mem.head _)
  have hpsi := PrfH_and_elim_left (PrfH_and_elim_left hctx)
  have hwT := PrfH_and_elim_right (PrfH_and_elim_left hctx)
  have hws := PrfH_and_elim_left (PrfH_and_elim_right hctx)
  have hwF := PrfH_and_elim_right (PrfH_and_elim_right hctx)
  have hshape := PrfH_and_elim_left hcl
  have hin1 := PrfH_and_elim_left (PrfH_and_elim_right hcl)
  have hin2 := PrfH_and_elim_right (PrfH_and_elim_right hcl)
  have hlt1 : PrfH [CTXFsubstfc wF wT s X, clBin wF X k] (lt (nthc X (numeralM 1)) X) :=
    PrfH.mp _ _ _ (prf_to_prfH (descenso_bin1 X k) _) hshape
  have hlt2 : PrfH [CTXFsubstfc wF wT s X, clBin wF X k] (lt (nthc X (numeralM 2)) X) :=
    PrfH.mp _ _ _ (prf_to_prfH (descenso_bin2 X k) _) hshape
  have hIH1 : PrfH [CTXFsubstfc wF wT s X, clBin wF X k]
      (targetSubstfc v s (nthc X (numeralM 1))) :=
    IH_at hpsi _ hlt1 wF wT v s
      (PrfH_and_intro hws (PrfH_and_intro (PrfH_and_intro hwT hwF) hin1))
  have hIH2 : PrfH [CTXFsubstfc wF wT s X, clBin wF X k]
      (targetSubstfc v s (nthc X (numeralM 2))) :=
    IH_at hpsi _ hlt2 wF wT v s
      (PrfH_and_intro hws (PrfH_and_intro (PrfH_and_intro hwT hwF) hin2))
  exact PrfH.mp _ _ _ (prf_to_prfH (hbin v s X) _)
    (PrfH_and_intro hshape (PrfH_and_intro hIH1 hIH2))

theorem rama_un (k : Nat) (hun : CasoUn k) (hwl : HasWitLift) :
    Prf (Formula.impl (clUn wF X k)
      (Formula.impl (CTXFsubstfc wF wT s X) (targetSubstfc v s X))) := by
  refine prf_deduction (deduction_aux ?_ (CTXFsubstfc wF wT s X) [clUn wF X k] rfl)
  have hcl : PrfH [CTXFsubstfc wF wT s X, clUn wF X k] (clUn wF X k) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hctx : PrfH [CTXFsubstfc wF wT s X, clUn wF X k] (CTXFsubstfc wF wT s X) :=
    PrfH.hyp _ _ (List.Mem.head _)
  have hpsi := PrfH_and_elim_left (PrfH_and_elim_left hctx)
  have hwT := PrfH_and_elim_right (PrfH_and_elim_left hctx)
  have hws := PrfH_and_elim_left (PrfH_and_elim_right hctx)
  have hwF := PrfH_and_elim_right (PrfH_and_elim_right hctx)
  have hshape := PrfH_and_elim_left hcl
  have hin1 := PrfH_and_elim_right hcl
  have hlt1 : PrfH [CTXFsubstfc wF wT s X, clUn wF X k] (lt (nthc X (numeralM 1)) X) :=
    PrfH.mp _ _ _ (prf_to_prfH (descenso_un X k) _) hshape
  -- el sustituyendo LEVANTADO conserva testigo
  have hwsl : PrfH [CTXFsubstfc wF wT s X, clUn wF X k] (hasWit (liftc zero s)) :=
    PrfH.mp _ _ _ (prf_to_prfH (hwl s) _) hws
  -- la HI se instancia con `v ↦ σv`, `s ↦ liftc 0 s` (van CUANTIFICADOS dentro de Φ)
  have hIH1 : PrfH [CTXFsubstfc wF wT s X, clUn wF X k]
      (targetSubstfc (succ v) (liftc zero s) (nthc X (numeralM 1))) :=
    IH_at hpsi _ hlt1 wF wT (succ v) (liftc zero s)
      (PrfH_and_intro hwsl (PrfH_and_intro (PrfH_and_intro hwT hwF) hin1))
  exact PrfH.mp _ _ _ (prf_to_prfH (hun v s X) _)
    (PrfH_and_intro hws (PrfH_and_intro hshape hIH1))

end Ramas

/-- **LAS OCHO RAMAS, ENSAMBLADAS** por or-elim al nivel `Prf` (sin cadenas de contexto). -/
theorem clauses_imp (hbot : CasoBot) (hatom : CasoAtom) (heq : CasoEq)
    (h5 : CasoBin 5) (h7 : CasoBin 7) (h8 : CasoBin 8)
    (h6 : CasoUn 6) (h9 : CasoUn 9) (hwl : HasWitLift) (wF wT v s X : Term) :
    Prf (Formula.impl (isFormCodeE2 wF wT X)
      (Formula.impl (CTXFsubstfc wF wT s X) (targetSubstfc v s X))) := by
  simp only [isFormCodeE2, lorAll]
  exact prf_or_elim_imp (rama_bot wF wT v s X hbot)
   (prf_or_elim_imp (rama_atom wF wT v s X hatom)
    (prf_or_elim_imp (rama_eq wF wT v s X heq)
     (prf_or_elim_imp (rama_bin wF wT v s X 5 h5)
      (prf_or_elim_imp (rama_un wF wT v s X 6 h6 hwl)
       (prf_or_elim_imp (rama_bin wF wT v s X 7 h7)
        (prf_or_elim_imp (rama_bin wF wT v s X 8 h8)
                         (rama_un wF wT v s X 9 h9 hwl)))))))

/-! ### El `PSI` levantado CUATRO veces (uno por binder interno) -/

/-- ⛔ ADR-019: los tres primeros escalones NO se reescriben aquí. `psi_lift_form`,
    `psi_lift_form2` y `psi_lift_form3` de `Meta/StrongInductionPrf.lean` son GENÉRICOS en `Φ`,
    y este frente es sólo una instancia con `Φ := PHIsubstfc`. El cuarto sí necesita una línea
    propia, porque pliega el resultado en la abreviatura local `PSIat`. -/
theorem psi_l4 : liftFormula 0 (liftFormula 0 (liftFormula 0 (liftFormula 0 (PSI PHIsubstfc))))
    = PSIat (.var 4) := by
  rw [psi_lift_form4 PHIsubstfc hPHIsubstfc]
  simp only [PSIat, lt, liftFormula, liftTerm, liftTerms, Nat.reduceAdd, Nat.reduceLT,
    reduceIte, hPHIsubstfc]

/-- **EL PASO DE LA INDUCCION FUERTE.** -/
theorem PHIsubstfc_step (hbot : CasoBot) (hatom : CasoAtom) (heq : CasoEq)
    (h5 : CasoBin 5) (h7 : CasoBin 7) (h8 : CasoBin 8)
    (h6 : CasoUn 6) (h9 : CasoUn 9) (hwl : HasWitLift) :
    Prf (Formula.forall (Formula.impl (PSI PHIsubstfc) PHIsubstfc)) := by
  refine Prf.gen _ (prf_deduction ?_)
  refine PrfH.gen [PSI PHIsubstfc] (Formula.forall (Formula.forall (Formula.forall PHIsubstfcBody))) ?_
  simp only [List.map_cons, List.map_nil]
  refine PrfH.gen _ (Formula.forall (Formula.forall PHIsubstfcBody)) ?_
  simp only [List.map_cons, List.map_nil]
  refine PrfH.gen _ (Formula.forall PHIsubstfcBody) ?_
  simp only [List.map_cons, List.map_nil]
  refine PrfH.gen _ PHIsubstfcBody ?_
  simp only [List.map_cons, List.map_nil, psi_l4]
  show PrfH [PSIat (.var 4)] PHIsubstfcBody
  refine deduction_aux ?_ (GUARD (.var 3) (.var 2) (.var 0) (.var 4)) [PSIat (.var 4)] rfl
  have hg : PrfH [GUARD (.var 3) (.var 2) (.var 0) (.var 4), PSIat (.var 4)]
      (GUARD (.var 3) (.var 2) (.var 0) (.var 4)) :=
    PrfH.hyp _ _ (List.Mem.head _)
  have hpsi : PrfH [GUARD (.var 3) (.var 2) (.var 0) (.var 4), PSIat (.var 4)]
      (PSIat (.var 4)) := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hws := PrfH_and_elim_left hg
  have hfc := PrfH_and_elim_right hg
  have hwT := PrfH_and_elim_left (PrfH_and_elim_left hfc)
  have hwF := PrfH_and_elim_right (PrfH_and_elim_left hfc)
  have hin := PrfH_and_elim_right hfc
  have hcode : PrfH [GUARD (.var 3) (.var 2) (.var 0) (.var 4), PSIat (.var 4)]
      (isFormCodeE2 (.var 3) (.var 2) (.var 4)) :=
    PrfH.mp _ _ _ (PrfH.mp _ _ _
      (prf_to_prfH (prf_isFormCodeE2_of_In (.var 3) (.var 2) (.var 4)) _) hin) hwF
  have hctx : PrfH [GUARD (.var 3) (.var 2) (.var 0) (.var 4), PSIat (.var 4)]
      (CTXFsubstfc (.var 3) (.var 2) (.var 0) (.var 4)) :=
    PrfH_and_intro (PrfH_and_intro hpsi hwT) (PrfH_and_intro hws hwF)
  exact PrfH.mp _ _ _ (PrfH.mp _ _ _
    (prf_to_prfH (clauses_imp hbot hatom heq h5 h7 h8 h6 h9 hwl
      (.var 3) (.var 2) (.var 1) (.var 0) (.var 4)) _) hcode) hctx

/-! ############################################################################
    ## §8 · EL TEOREMA — `pcc_eval_substfc` GUARDADO, argumentos ABSTRACTOS
    ############################################################################ -/

theorem PHIsubstfc_all (hbot : CasoBot) (hatom : CasoAtom) (heq : CasoEq)
    (h5 : CasoBin 5) (h7 : CasoBin 7) (h8 : CasoBin 8)
    (h6 : CasoUn 6) (h9 : CasoUn 9) (hwl : HasWitLift) (t : Term) :
    Prf (substFormula 0 t PHIsubstfc) :=
  prf_strong_induction PHIsubstfc hPHIsubstfc (PHIsubstfc_step hbot hatom heq h5 h7 h8 h6 h9 hwl) t

theorem DESCENSO_substfc_imp (hbot : CasoBot) (hatom : CasoAtom) (heq : CasoEq)
    (h5 : CasoBin 5) (h7 : CasoBin 7) (h8 : CasoBin 8)
    (h6 : CasoUn 6) (h9 : CasoUn 9) (hwl : HasWitLift) (wF wT v s t : Term) :
    Prf (Formula.impl (GUARD wF wT s t) (targetSubstfc v s t)) :=
  prfH_nil_to_prf
    (PHIsubstfc_use t wF wT v s
      (prf_to_prfH (PHIsubstfc_all hbot hatom heq h5 h7 h8 h6 h9 hwl t) [])) rfl

/-- **`pcc_eval_substfc`** — la evaluacion provable de `substfc` con `v`, `s`, `f`
    ABSTRACTOS, guardada por los DOS testigos (formula y termino), MODULO los 8 casos. -/
theorem pcc_eval_substfc_modulo_8
    (hbot : CasoBot) (hatom : CasoAtom) (heq : CasoEq)
    (h5 : CasoBin 5) (h7 : CasoBin 7) (h8 : CasoBin 8)
    (h6 : CasoUn 6) (h9 : CasoUn 9) (hwl : HasWitLift)
    (wF wT v s f : Term) (hws : Prf (hasWit s)) (hfc : Prf (isFC1 wF wT f)) :
    Prf (provFromCode (eqc (substfcT (tcFn v) (tcFn s) (tcFn f)) (tcFn (substfc v s f)))) :=
  prf_mp (DESCENSO_substfc_imp hbot hatom heq h5 h7 h8 h6 h9 hwl wF wT v s f)
    (prf_and_intro hws hfc)

/-! ############################################################################
    ## §9 · DESCARGA de `CasoBot` y de `CasoBin 5/7/8`.

    Copia LITERAL de `sondeos/SubstfcPlanos.lean` §0-§6 (que compila net-0), mas UNA
    pieza nueva: `paso2_caso_bin_imp`, que es `paso2_caso_bin` reescrito en `PrfH Γ`
    — hace falta porque la HI de la induccion llega como HIPOTESIS del contexto, no
    como teorema `Prf` cerrado.
    ############################################################################ -/

/-! ### §9.1 · CASO `bottom` -/

/-- **`CasoBot` DESCARGADO** (Leibniz desde la forma ecuacional). -/
theorem casoBot : CasoBot := by
  intro v s X
  refine prf_deduction ?_
  exact PrfH_congr_targetSubstfc (PrfH_eq_symm (prfH_hyp_self (shapeNul X 2)))
    (prf_to_prfH (paso2_caso_bottom v s) _)

/-! ### §9.2 · CASO BINARIO (`implc`/`andc`/`orc`) -/

/-- **PIEZA NUEVA**: `SubstfcPlanos.paso2_caso_bin` reescrito en forma IMPLICACION
    (`PrfH Γ`), porque en la induccion la HI llega como HIPOTESIS, no como `Prf` cerrada. -/
theorem paso2_caso_bin_imp (k : Nat) (v s a b : Term)
    (hax : Prf (provFromCode (eqCodeFn
      (substfcT (tcFn v) (tcFn s) (binT k (tcFn a) (tcFn b)))
      (binT k (substfcT (tcFn v) (tcFn s) (tcFn a)) (substfcT (tcFn v) (tcFn s) (tcFn b))))))
    (hobj : Prf (substfc v s (cons (numeralM k) (cons a (cons b nil)))
      =eq cons (numeralM k) (cons (substfc v s a) (cons (substfc v s b) nil)))) :
    Prf (Formula.impl (land (targetSubstfc v s a) (targetSubstfc v s b))
      (targetSubstfc v s (cons (numeralM k) (cons a (cons b nil))))) := by
  refine prf_deduction ?_
  have hh := prfH_hyp_self (land (targetSubstfc v s a) (targetSubstfc v s b))
  have hA : PrfH [land (targetSubstfc v s a) (targetSubstfc v s b)]
      (provFromCode (eqc (substfcT (tcFn v) (tcFn s) (tcFn a)) (tcFn (substfc v s a)))) :=
    PrfH_and_elim_left hh
  have hB : PrfH [land (targetSubstfc v s a) (targetSubstfc v s b)]
      (provFromCode (eqc (substfcT (tcFn v) (tcFn s) (tcFn b)) (tcFn (substfc v s b)))) :=
    PrfH_and_elim_right hh
  have iSA : ∀ W, Prf (substtc zero W (substfcT (tcFn v) (tcFn s) (tcFn a))
      =eq substfcT (tcFn v) (tcFn s) (tcFn a)) :=
    substtc_inv_substfcT (substtc_inv_tcFn v) (substtc_inv_tcFn s) (substtc_inv_tcFn a)
  have iSB : ∀ W, Prf (substtc zero W (substfcT (tcFn v) (tcFn s) (tcFn b))
      =eq substfcT (tcFn v) (tcFn s) (tcFn b)) :=
    substtc_inv_substfcT (substtc_inv_tcFn v) (substtc_inv_tcFn s) (substtc_inv_tcFn b)
  have iX0 : ∀ W, Prf (substtc zero W
        (substfcT (tcFn v) (tcFn s) (tcFn (cons (numeralM k) (cons a (cons b nil)))))
      =eq substfcT (tcFn v) (tcFn s) (tcFn (cons (numeralM k) (cons a (cons b nil))))) :=
    substtc_inv_substfcT (substtc_inv_tcFn v) (substtc_inv_tcFn s)
      (substtc_inv_tcFn (cons (numeralM k) (cons a (cons b nil))))
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
  have h1 := prf_to_prfH (prf_mp (pcc_congr_substfcT_arg3_code (tcFn v) (tcFn s)
      (tcFn (cons (numeralM k) (cons a (cons b nil)))) (binT k (tcFn a) (tcFn b))
      (substtc_inv_tcFn v) (substtc_inv_tcFn s)
      (substtc_inv_tcFn (cons (numeralM k) (cons a (cons b nil)))))
    (pcc_dot_bin_symm k a b)) [land (targetSubstfc v s a) (targetSubstfc v s b)]
  have h2 := prf_to_prfH hax [land (targetSubstfc v s a) (targetSubstfc v s b)]
  have h3 := PrfH.mp _ _ _ (prf_to_prfH (pcc_congr_binT_1_code k
      (substfcT (tcFn v) (tcFn s) (tcFn b))
      (substfcT (tcFn v) (tcFn s) (tcFn a)) (tcFn (substfc v s a)) iSB iSA) _) hA
  have h4 := PrfH.mp _ _ _ (prf_to_prfH (pcc_congr_binT_2_code k (tcFn (substfc v s a))
      (substfcT (tcFn v) (tcFn s) (tcFn b)) (tcFn (substfc v s b))
      (substtc_inv_tcFn (substfc v s a)) iSB) _) hB
  have h5 := prf_to_prfH (pcc_dot_bin k (substfc v s a) (substfc v s b))
    [land (targetSubstfc v s a) (targetSubstfc v s b)]
  have h6 := prf_to_prfH (prf_mp (prf_provCode_congr (prf_congr_eqCodeFn (prf_refl _)
      (prf_congr_tcFn (prf_eq_symm hobj))))
    (prf_provFromCode_eqCodeFn_refl
      (tcFn (cons (numeralM k) (cons (substfc v s a) (cons (substfc v s b) nil))))))
    [land (targetSubstfc v s a) (targetSubstfc v s b)]
  refine PrfH_eq_trans_code _ _ _ iX0 h1
    (PrfH_eq_trans_code _ _ _ iX1 h2
      (PrfH_eq_trans_code _ _ _ iX2 h3
        (PrfH_eq_trans_code _ _ _ iX3 h4
          (PrfH_eq_trans_code _ _ _ iX4 h5 h6 ?_ ?_ ?_) ?_ ?_ ?_) ?_ ?_ ?_) ?_ ?_ ?_) ?_ ?_ ?_
    <;> hw_auto

/-- **`CasoBin k` DESCARGADO**, generico en el tag. -/
theorem casoBin_gen (k : Nat)
    (hax : ∀ v s a b : Term, Prf (provFromCode (eqCodeFn
      (substfcT (tcFn v) (tcFn s) (binT k (tcFn a) (tcFn b)))
      (binT k (substfcT (tcFn v) (tcFn s) (tcFn a)) (substfcT (tcFn v) (tcFn s) (tcFn b))))))
    (hobj : ∀ v s a b : Term, Prf (substfc v s (cons (numeralM k) (cons a (cons b nil)))
      =eq cons (numeralM k) (cons (substfc v s a) (cons (substfc v s b) nil)))) :
    CasoBin k := by
  intro v s X
  refine prf_deduction ?_
  have hh := prfH_hyp_self (land (shapeBin X k)
    (land (targetSubstfc v s (nthc X (numeralM 1))) (targetSubstfc v s (nthc X (numeralM 2)))))
  have hshape := PrfH_and_elim_left hh
  have hab := PrfH_and_elim_right hh
  have hC := PrfH.mp _ _ _
    (prf_to_prfH (paso2_caso_bin_imp k v s (nthc X (numeralM 1)) (nthc X (numeralM 2))
      (hax v s (nthc X (numeralM 1)) (nthc X (numeralM 2)))
      (hobj v s (nthc X (numeralM 1)) (nthc X (numeralM 2)))) _) hab
  exact PrfH_congr_targetSubstfc (PrfH_eq_symm hshape) hC

theorem casoBin5 : CasoBin 5 :=
  casoBin_gen 5
    (fun v s a b => pcc_substfc_bin_dot (numeralM 5) (fun c => liftTerm_numeralM c 5)
      (show ax_substfc_impl ∈ axioms by simp [axioms]) v s a b)
    (fun v s a b => prf_substfc_impl v s a b)

theorem casoBin7 : CasoBin 7 :=
  casoBin_gen 7
    (fun v s a b => pcc_substfc_bin_dot (numeralM 7) (fun c => liftTerm_numeralM c 7)
      (show ax_substfc_and ∈ axioms by simp [axioms]) v s a b)
    (fun v s a b => prf_substfc_and v s a b)

theorem casoBin8 : CasoBin 8 :=
  casoBin_gen 8
    (fun v s a b => pcc_substfc_bin_dot (numeralM 8) (fun c => liftTerm_numeralM c 8)
      (show ax_substfc_or ∈ axioms by simp [axioms]) v s a b)
    (fun v s a b => prf_substfc_or v s a b)

/-- **EL TEOREMA CON CUATRO HIPOTESIS MENOS**: quedan `CasoAtom`, `CasoEq`,
    `CasoUn 6`, `CasoUn 9` y `HasWitLift`. -/
theorem pcc_eval_substfc_modulo_5
    (hatom : CasoAtom) (heq : CasoEq) (h6 : CasoUn 6) (h9 : CasoUn 9) (hwl : HasWitLift)
    (wF wT v s f : Term) (hws : Prf (hasWit s)) (hfc : Prf (isFC1 wF wT f)) :
    Prf (provFromCode (eqc (substfcT (tcFn v) (tcFn s) (tcFn f)) (tcFn (substfc v s f)))) :=
  pcc_eval_substfc_modulo_8 casoBot hatom heq casoBin5 casoBin7 casoBin8 h6 h9 hwl
    wF wT v s f hws hfc

/-! ############################################################################
    ## §10 · DESCARGA de `HasWitLift` — copia LITERAL de
       `sondeos/ClausuraLiftSinWTs.lean` §3-§4 (`prf_lenc_liftsc`, `prf_nthc_liftsc`,
       `prf_In_liftsc`, `prf_argsIn_lift`, `prf_isTermCodeE1_lift`, `prf_wfAll1_lift`,
       `prf_isTC1_lift`) mas `CRIT_hasWit_lift`.
    ############################################################################ -/

/-! ## 3 · `liftsc zero` ES EL MAP POSICIONAL — por INDUCCION DE LISTAS (`Prf.listInd`)

    🔑 Esto es lo que hace viable la via: `liftsc` esta axiomatizado SOLO en `nil`/`cons`
    (`ax_liftsc_nil` / `ax_liftsc_cons`), y el testigo se lee POSICIONALMENTE (`lenc`/`nthc`).
    El puente entre las dos lecturas es `prf_list_induction`, que es la regla `Prf.listInd`
    del calculo (NO un axioma de Lean, NO un simbolo nuevo). -/

/-! ### G1 · `lenc (liftsc 0 L) ≐ lenc L`, para `L` ARBITRARIO -/

/-! ### G2 · `i < lenc L → nthc (liftsc 0 L) i ≐ liftc 0 (nthc L i)` -/

/-! ### G3 · `In x w ⇒ In (liftc 0 x) (liftsc 0 w)` -/

/-! ## 4 · CLAUSURA DEL PREDICADO BAJO `liftc zero` — el testigo nuevo es `liftsc zero w` -/

/-! ### EL LEMA CLAVE — los DOS disyuntos sobreviven al `liftc zero` -/

/-! ### LA CLAUSURA -/

/-- **`HasWitLift` DESCARGADO** (`CRIT_hasWit_lift`). -/
theorem casoHasWitLift : HasWitLift := by
  intro c
  refine prf_ex_elim_imp ?_
  have hgoal : liftFormula 0 (hasWit (liftc zero c))
      = Formula.ex (isTC1 (.var 0) (liftTerm 1 (liftTerm 0 (liftc zero c)))) := by
    simp only [hasWit, liftFormula, liftF_isTC1, liftTerm, Nat.reduceAdd,
      Nat.zero_lt_succ, reduceIte]
  rw [hgoal]
  refine PrfH_ex_intro (liftsc zero (.var 0)) ?_
  have hsub : substFormula 0 (liftsc zero (.var 0))
      (isTC1 (.var 0) (liftTerm 1 (liftTerm 0 (liftc zero c))))
      = isTC1 (liftsc zero (.var 0)) (liftc zero (liftTerm 0 c)) := by
    have hv : substTerm 0 (liftsc zero (Term.var 0)) (Term.var 0) = liftsc zero (.var 0) := by
      simp only [substTerm, if_true]
    rw [← FOL.liftTerm_comm_zero, substF_isTC1, FOL.substTerm_liftTerm, hv, liftT_liftc]
  rw [hsub]
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_isTC1_lift (.var 0) (liftTerm 0 c)) _)
    (prfH_hyp_self _)

/-- **EL TEOREMA CON CINCO HIPOTESIS MENOS**: quedan SOLO `CasoAtom`, `CasoEq`,
    `CasoUn 6` y `CasoUn 9` — los CUATRO constructores de `substfc` que no estaban
    disponibles en la forma IMPLICACION que la induccion consume. -/
theorem pcc_eval_substfc_modulo_4
    (hatom : CasoAtom) (heq : CasoEq) (h6 : CasoUn 6) (h9 : CasoUn 9)
    (wF wT v s f : Term) (hws : Prf (hasWit s)) (hfc : Prf (isFC1 wF wT f)) :
    Prf (provFromCode (eqc (substfcT (tcFn v) (tcFn s) (tcFn f)) (tcFn (substfc v s f)))) :=
  pcc_eval_substfc_modulo_8 casoBot hatom heq casoBin5 casoBin7 casoBin8 h6 h9
    casoHasWitLift wF wT v s f hws hfc

/-! ############################################################################
    ## §11 · DESCARGA de `CasoEq` y `CasoAtom` — LO QUE **NO** EXISTIA.

    Ni `pcc_substfc_eq_dot` ni `pcc_substfc_atom_dot` estaban en `sondeos/` ni en
    produccion (grep sobre el arbol entero: cero apariciones). Lo que si existia es la
    parte de TERMINO (`DESCENSO_imp` / `DESCENSO_lista_imp`, copiadas arriba).

    EL PUENTE «del testigo de FORMULA sale el testigo de TERMINO para sus subcodigos»
    NO HACE FALTA: se DISUELVE por construccion. La guarda `isFC1 wF wT c` lleva DENTRO
    `wfAll1 wT`, y las clausulas `clEq`/`clAtom` piden `In (nthc X i) wT` / `argsIn wT ...`
    — que es LITERALMENTE `isTC1 wT (nthc X i)` y la premisa de
    `DESCENSO_lista_imp`. Los puentes `:= rfl` de abajo lo certifican.
    ############################################################################ -/

/-- La evaluacion provable de `substtc`, en forma IMPLICACION y SIN hipotesis. -/
theorem eval_substtc_imp (w v s t : Term) :
    Prf (Formula.impl (isTC1 w t) (targetSubsttc v s t)) :=
  DESCENSO_substtc_imp w v s t

/-- Su gemela sobre LISTAS de codigos de termino. -/
theorem eval_substtsc_imp (w v s t : Term) :
    Prf (Formula.impl (land (wfAll1 w) (argsIn w t)) (targetSubsttsc v s t)) :=
  DESCENSO_substtc_lista_imp w v s t

/-! ### §11.1 · La funcion ternaria GENERICA (para escribir UN solo lema `dot`) -/

def gO (nm : String) (v s f : Term) : Term := Term.func nm [v, s, f]
def gT (nm : String) (v s f : Term) : Term :=
  funcc (strCode nm) (cons v (cons s (cons f nil)))

theorem prf_congr_gT (nm : String) {v v' s s' f f' : Term}
    (hv : Prf (v =eq v')) (hs : Prf (s =eq s')) (hf : Prf (f =eq f')) :
    Prf (gT nm v s f =eq gT nm v' s' f') := prf_congr_funcc3 hv hs hf

theorem prf_substtc_gT (nm : String) (v W x y z : Term) :
    Prf (substtc v W (gT nm x y z)
      =eq gT nm (substtc v W x) (substtc v W y) (substtc v W z)) :=
  prf_substtc_funcc3 v W (strCode nm) x y z

theorem substtc_inv_gT (nm : String) {X Y Z : Term}
    (hX : ∀ W, Prf (substtc zero W X =eq X)) (hY : ∀ W, Prf (substtc zero W Y =eq Y))
    (hZ : ∀ W, Prf (substtc zero W Z =eq Z)) :
    ∀ W, Prf (substtc zero W (gT nm X Y Z) =eq gT nm X Y Z) := fun W =>
  prf_eq_trans (prf_substtc_gT nm zero W X Y Z) (prf_congr_gT nm (hX W) (hY W) (hZ W))

/-! ### §11.2 · `pcc_substfc_ter_dot` — la instancia INTERNA de un axioma
    `substfc v s (⟨T⟩ a b) ≐ ⟨T⟩ (F v s a) (F v s b)` con `F` GENERICA.
    Con `F = substfc` reproduce `pcc_substfc_bin_dot`; con `F = substtc` da `eqc`. -/

def AXTER_BODY (T : Term) (nm : String) : Formula :=
  substfc (.var 3) (.var 2) (binct T (.var 1) (.var 0))
    =eq binct T (gO nm (.var 3) (.var 2) (.var 1)) (gO nm (.var 3) (.var 2) (.var 0))

theorem AXTER_eq : ax_substfc_eq = forall_4 (AXTER_BODY (numeralM 4) "substtc") := rfl
theorem AXTER_impl : ax_substfc_impl = forall_4 (AXTER_BODY (numeralM 5) "substfc") := rfl

theorem pcc_substfc_ter_dot (T : Term) (nm : String) (hT : ∀ c : Nat, liftTerm c T = T)
    (hmem : forall_4 (AXTER_BODY T nm) ∈ axioms) (v s a b : Term) :
    Prf (provFromCode (eqCodeFn
      (substfcT (tcFn v) (tcFn s) (binK (termCode T) (tcFn a) (tcFn b)))
      (binK (termCode T) (gT nm (tcFn v) (tcFn s) (tcFn a))
        (gT nm (tcFn v) (tcFn s) (tcFn b))))) := by
  let W3 : Term := liftc zero (liftc zero (liftc zero (tcFn v)))
  let W2 : Term := liftc zero (liftc zero (tcFn s))
  let W1 : Term := liftc zero (tcFn a)
  let W0 : Term := tcFn b
  have hv3 : Prf (W3 =eq tcFn v) :=
    prf_eq_trans (ROBINSON_PlusPlus.Meta.NumCodeClosedPrf.prf_congr_liftc
      (prf_eq_trans (ROBINSON_PlusPlus.Meta.NumCodeClosedPrf.prf_congr_liftc (prf_liftc_tcFn v)) (prf_liftc_tcFn v)))
      (prf_liftc_tcFn v)
  have hs2 : Prf (W2 =eq tcFn s) :=
    prf_eq_trans (ROBINSON_PlusPlus.Meta.NumCodeClosedPrf.prf_congr_liftc (prf_liftc_tcFn s)) (prf_liftc_tcFn s)
  have ha1 : Prf (W1 =eq tcFn a) := prf_liftc_tcFn a
  have hkc : substCodeT 3 W3 T = termCode T := substCodeT_closed 3 W3 T hT
  have hin0 : Prf (substfc (numeral 3) W3 (formCode (AXTER_BODY T nm))
      =eq eqCodeFn
        (substfcT W3 (varc (numeral 2))
          (binK (substCodeT 3 W3 T) (varc (numeral 1)) (varc (numeral 0))))
        (binK (substCodeT 3 W3 T) (gT nm W3 (varc (numeral 2)) (varc (numeral 1)))
          (gT nm W3 (varc (numeral 2)) (varc (numeral 0))))) :=
    prf_substfc_arith_open 3 W3 (AXTER_BODY T nm)
  rw [hkc] at hin0
  have hnorm3 : Prf (eqCodeFn
        (substfcT W3 (varc (numeral 2))
          (binK (termCode T) (varc (numeral 1)) (varc (numeral 0))))
        (binK (termCode T) (gT nm W3 (varc (numeral 2)) (varc (numeral 1)))
          (gT nm W3 (varc (numeral 2)) (varc (numeral 0))))
      =eq eqCodeFn
        (substfcT (tcFn v) (varc (numeral 2))
          (binK (termCode T) (varc (numeral 1)) (varc (numeral 0))))
        (binK (termCode T) (gT nm (tcFn v) (varc (numeral 2)) (varc (numeral 1)))
          (gT nm (tcFn v) (varc (numeral 2)) (varc (numeral 0))))) :=
    prf_congr_eqCodeFn
      (prf_congr_substfcT hv3 (prf_refl _) (prf_refl _))
      (prf_congr_binK (prf_congr_gT nm hv3 (prf_refl _) (prf_refl _))
        (prf_congr_gT nm hv3 (prf_refl _) (prf_refl _)))
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
        (binK (termCode T) (gT nm (tcFn v) (varc (numeral 2)) (varc (numeral 1)))
          (gT nm (tcFn v) (varc (numeral 2)) (varc (numeral 0)))))
      =eq eqCodeFn
        (substfcT (tcFn v) (tcFn s) (binK (termCode T) (varc (numeral 1)) (varc (numeral 0))))
        (binK (termCode T) (gT nm (tcFn v) (tcFn s) (varc (numeral 1)))
          (gT nm (tcFn v) (tcFn s) (varc (numeral 0))))) := by
    refine prf_eq_trans (prf_substfc_eq (numeral 2) W2 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_substfcT (numeral 2) W2 _ _ _) ?_
      refine prf_congr_substfcT k2v k2s ?_
      exact prf_eq_trans (prf_substtc_binK_at T hT 2 W2 _ _) (prf_congr_binK k21 k20)
    · refine prf_eq_trans (prf_substtc_binK_at T hT 2 W2 _ _) ?_
      refine prf_congr_binK ?_ ?_
      · exact prf_eq_trans (prf_substtc_gT nm (numeral 2) W2 _ _ _)
          (prf_congr_gT nm k2v k2s k21)
      · exact prf_eq_trans (prf_substtc_gT nm (numeral 2) W2 _ _ _)
          (prf_congr_gT nm k2v k2s k20)
  have k1v : Prf (substtc (numeral 1) W1 (tcFn v) =eq tcFn v) := prf_substtc_tcFn_at 1 W1 v
  have k1s : Prf (substtc (numeral 1) W1 (tcFn s) =eq tcFn s) := prf_substtc_tcFn_at 1 W1 s
  have k1a : Prf (substtc (numeral 1) W1 (varc (numeral 1)) =eq tcFn a) :=
    prf_eq_trans (prf_mp (prf_substtc_var_eq (numeral 1) W1 (numeral 1)) (prf_refl _)) ha1
  have k10 : Prf (substtc (numeral 1) W1 (varc (numeral 0)) =eq varc (numeral 0)) :=
    prf_mp (prf_substtc_var_lt (numeral 1) W1 (numeral 0))
      (prf_gnum_lt (show (0 : Nat) < 1 by omega))
  have hmid1 : Prf (substfc (numeral 1) W1 (eqCodeFn
        (substfcT (tcFn v) (tcFn s) (binK (termCode T) (varc (numeral 1)) (varc (numeral 0))))
        (binK (termCode T) (gT nm (tcFn v) (tcFn s) (varc (numeral 1)))
          (gT nm (tcFn v) (tcFn s) (varc (numeral 0)))))
      =eq eqCodeFn
        (substfcT (tcFn v) (tcFn s) (binK (termCode T) (tcFn a) (varc (numeral 0))))
        (binK (termCode T) (gT nm (tcFn v) (tcFn s) (tcFn a))
          (gT nm (tcFn v) (tcFn s) (varc (numeral 0))))) := by
    refine prf_eq_trans (prf_substfc_eq (numeral 1) W1 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_substfcT (numeral 1) W1 _ _ _) ?_
      refine prf_congr_substfcT k1v k1s ?_
      exact prf_eq_trans (prf_substtc_binK_at T hT 1 W1 _ _) (prf_congr_binK k1a k10)
    · refine prf_eq_trans (prf_substtc_binK_at T hT 1 W1 _ _) ?_
      refine prf_congr_binK ?_ ?_
      · exact prf_eq_trans (prf_substtc_gT nm (numeral 1) W1 _ _ _)
          (prf_congr_gT nm k1v k1s k1a)
      · exact prf_eq_trans (prf_substtc_gT nm (numeral 1) W1 _ _ _)
          (prf_congr_gT nm k1v k1s k10)
  have k0v : Prf (substtc zero W0 (tcFn v) =eq tcFn v) := prf_substtc_tcFn W0 v
  have k0s : Prf (substtc zero W0 (tcFn s) =eq tcFn s) := prf_substtc_tcFn W0 s
  have k0a : Prf (substtc zero W0 (tcFn a) =eq tcFn a) := prf_substtc_tcFn W0 a
  have k0b : Prf (substtc zero W0 (varc (numeral 0)) =eq tcFn b) := prf_substtc_varc0 W0
  have hout : Prf (substfc zero W0 (eqCodeFn
        (substfcT (tcFn v) (tcFn s) (binK (termCode T) (tcFn a) (varc (numeral 0))))
        (binK (termCode T) (gT nm (tcFn v) (tcFn s) (tcFn a))
          (gT nm (tcFn v) (tcFn s) (varc (numeral 0)))))
      =eq eqCodeFn
        (substfcT (tcFn v) (tcFn s) (binK (termCode T) (tcFn a) (tcFn b)))
        (binK (termCode T) (gT nm (tcFn v) (tcFn s) (tcFn a))
          (gT nm (tcFn v) (tcFn s) (tcFn b)))) := by
    refine prf_eq_trans (prf_substfc_eq zero W0 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_substfcT zero W0 _ _ _) ?_
      refine prf_congr_substfcT k0v k0s ?_
      exact prf_eq_trans (prf_substtc_binK_at T hT 0 W0 _ _) (prf_congr_binK k0a k0b)
    · refine prf_eq_trans (prf_substtc_binK_at T hT 0 W0 _ _) ?_
      refine prf_congr_binK ?_ ?_
      · exact prf_eq_trans (prf_substtc_gT nm zero W0 _ _ _)
          (prf_congr_gT nm k0v k0s k0a)
      · exact prf_eq_trans (prf_substtc_gT nm zero W0 _ _ _)
          (prf_congr_gT nm k0v k0s k0b)
  have hchain : Prf (substfc zero W0 (substfc (numeral 1) W1 (substfc (numeral 2) W2
        (substfc (numeral 3) W3 (formCode (AXTER_BODY T nm)))))
      =eq eqCodeFn
        (substfcT (tcFn v) (tcFn s) (binK (termCode T) (tcFn a) (tcFn b)))
        (binK (termCode T) (gT nm (tcFn v) (tcFn s) (tcFn a))
          (gT nm (tcFn v) (tcFn s) (tcFn b)))) :=
    prf_eq_trans (prf_congr_substfc_arg3
      (prf_eq_trans (prf_congr_substfc_arg3
        (prf_eq_trans (prf_congr_substfc_arg3 (prf_eq_trans hin0 hnorm3)) hmid2)) hmid1)) hout
  exact prf_mp (prf_provCode_congr hchain)
    (pcc_axiom_inst4 (AXTER_BODY T nm) hmem (tcFn v) (tcFn s) (tcFn a) (tcFn b)
      (by hw_auto) (by hw_auto) (by hw_auto) (by hw_auto))

/-! ### §11.3 · `pcc_substfc_atom_dot` — el axioma `atomc`, cuya PRIMERA casilla
    (el simbolo de predicado) es OPACA y no se toca. -/

def AXATOM_BODY : Formula :=
  substfc (.var 3) (.var 2) (binct (numeralM 3) (.var 1) (.var 0))
    =eq binct (numeralM 3) (.var 1) (gO "substtsc" (.var 3) (.var 2) (.var 0))

theorem AXATOM_ok : ax_substfc_atom = forall_4 AXATOM_BODY := rfl

theorem pcc_substfc_atom_dot (v s a b : Term) :
    Prf (provFromCode (eqCodeFn
      (substfcT (tcFn v) (tcFn s) (binT 3 (tcFn a) (tcFn b)))
      (binT 3 (tcFn a) (substtscT (tcFn v) (tcFn s) (tcFn b))))) := by
  let T : Term := numeralM 3
  have hT : ∀ c : Nat, liftTerm c T = T := fun c => liftTerm_numeralM c 3
  let W3 : Term := liftc zero (liftc zero (liftc zero (tcFn v)))
  let W2 : Term := liftc zero (liftc zero (tcFn s))
  let W1 : Term := liftc zero (tcFn a)
  let W0 : Term := tcFn b
  have hv3 : Prf (W3 =eq tcFn v) :=
    prf_eq_trans (ROBINSON_PlusPlus.Meta.NumCodeClosedPrf.prf_congr_liftc
      (prf_eq_trans (ROBINSON_PlusPlus.Meta.NumCodeClosedPrf.prf_congr_liftc (prf_liftc_tcFn v)) (prf_liftc_tcFn v)))
      (prf_liftc_tcFn v)
  have hs2 : Prf (W2 =eq tcFn s) :=
    prf_eq_trans (ROBINSON_PlusPlus.Meta.NumCodeClosedPrf.prf_congr_liftc (prf_liftc_tcFn s)) (prf_liftc_tcFn s)
  have ha1 : Prf (W1 =eq tcFn a) := prf_liftc_tcFn a
  have hkc : substCodeT 3 W3 T = termCode T := substCodeT_closed 3 W3 T hT
  have hin0 : Prf (substfc (numeral 3) W3 (formCode AXATOM_BODY)
      =eq eqCodeFn
        (substfcT W3 (varc (numeral 2))
          (binK (substCodeT 3 W3 T) (varc (numeral 1)) (varc (numeral 0))))
        (binK (substCodeT 3 W3 T) (varc (numeral 1))
          (gT "substtsc" W3 (varc (numeral 2)) (varc (numeral 0))))) :=
    prf_substfc_arith_open 3 W3 AXATOM_BODY
  rw [hkc] at hin0
  have hnorm3 : Prf (eqCodeFn
        (substfcT W3 (varc (numeral 2))
          (binK (termCode T) (varc (numeral 1)) (varc (numeral 0))))
        (binK (termCode T) (varc (numeral 1))
          (gT "substtsc" W3 (varc (numeral 2)) (varc (numeral 0))))
      =eq eqCodeFn
        (substfcT (tcFn v) (varc (numeral 2))
          (binK (termCode T) (varc (numeral 1)) (varc (numeral 0))))
        (binK (termCode T) (varc (numeral 1))
          (gT "substtsc" (tcFn v) (varc (numeral 2)) (varc (numeral 0))))) :=
    prf_congr_eqCodeFn
      (prf_congr_substfcT hv3 (prf_refl _) (prf_refl _))
      (prf_congr_binK (prf_refl _) (prf_congr_gT _ hv3 (prf_refl _) (prf_refl _)))
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
        (binK (termCode T) (varc (numeral 1))
          (gT "substtsc" (tcFn v) (varc (numeral 2)) (varc (numeral 0)))))
      =eq eqCodeFn
        (substfcT (tcFn v) (tcFn s) (binK (termCode T) (varc (numeral 1)) (varc (numeral 0))))
        (binK (termCode T) (varc (numeral 1))
          (gT "substtsc" (tcFn v) (tcFn s) (varc (numeral 0))))) := by
    refine prf_eq_trans (prf_substfc_eq (numeral 2) W2 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_substfcT (numeral 2) W2 _ _ _) ?_
      refine prf_congr_substfcT k2v k2s ?_
      exact prf_eq_trans (prf_substtc_binK_at T hT 2 W2 _ _) (prf_congr_binK k21 k20)
    · refine prf_eq_trans (prf_substtc_binK_at T hT 2 W2 _ _) ?_
      refine prf_congr_binK k21 ?_
      exact prf_eq_trans (prf_substtc_gT _ (numeral 2) W2 _ _ _)
        (prf_congr_gT _ k2v k2s k20)
  have k1v : Prf (substtc (numeral 1) W1 (tcFn v) =eq tcFn v) := prf_substtc_tcFn_at 1 W1 v
  have k1s : Prf (substtc (numeral 1) W1 (tcFn s) =eq tcFn s) := prf_substtc_tcFn_at 1 W1 s
  have k1a : Prf (substtc (numeral 1) W1 (varc (numeral 1)) =eq tcFn a) :=
    prf_eq_trans (prf_mp (prf_substtc_var_eq (numeral 1) W1 (numeral 1)) (prf_refl _)) ha1
  have k10 : Prf (substtc (numeral 1) W1 (varc (numeral 0)) =eq varc (numeral 0)) :=
    prf_mp (prf_substtc_var_lt (numeral 1) W1 (numeral 0))
      (prf_gnum_lt (show (0 : Nat) < 1 by omega))
  have hmid1 : Prf (substfc (numeral 1) W1 (eqCodeFn
        (substfcT (tcFn v) (tcFn s) (binK (termCode T) (varc (numeral 1)) (varc (numeral 0))))
        (binK (termCode T) (varc (numeral 1))
          (gT "substtsc" (tcFn v) (tcFn s) (varc (numeral 0)))))
      =eq eqCodeFn
        (substfcT (tcFn v) (tcFn s) (binK (termCode T) (tcFn a) (varc (numeral 0))))
        (binK (termCode T) (tcFn a)
          (gT "substtsc" (tcFn v) (tcFn s) (varc (numeral 0))))) := by
    refine prf_eq_trans (prf_substfc_eq (numeral 1) W1 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_substfcT (numeral 1) W1 _ _ _) ?_
      refine prf_congr_substfcT k1v k1s ?_
      exact prf_eq_trans (prf_substtc_binK_at T hT 1 W1 _ _) (prf_congr_binK k1a k10)
    · refine prf_eq_trans (prf_substtc_binK_at T hT 1 W1 _ _) ?_
      refine prf_congr_binK k1a ?_
      exact prf_eq_trans (prf_substtc_gT _ (numeral 1) W1 _ _ _)
        (prf_congr_gT _ k1v k1s k10)
  have k0v : Prf (substtc zero W0 (tcFn v) =eq tcFn v) := prf_substtc_tcFn W0 v
  have k0s : Prf (substtc zero W0 (tcFn s) =eq tcFn s) := prf_substtc_tcFn W0 s
  have k0a : Prf (substtc zero W0 (tcFn a) =eq tcFn a) := prf_substtc_tcFn W0 a
  have k0b : Prf (substtc zero W0 (varc (numeral 0)) =eq tcFn b) := prf_substtc_varc0 W0
  have hout : Prf (substfc zero W0 (eqCodeFn
        (substfcT (tcFn v) (tcFn s) (binK (termCode T) (tcFn a) (varc (numeral 0))))
        (binK (termCode T) (tcFn a)
          (gT "substtsc" (tcFn v) (tcFn s) (varc (numeral 0)))))
      =eq eqCodeFn
        (substfcT (tcFn v) (tcFn s) (binK (termCode T) (tcFn a) (tcFn b)))
        (binK (termCode T) (tcFn a) (gT "substtsc" (tcFn v) (tcFn s) (tcFn b)))) := by
    refine prf_eq_trans (prf_substfc_eq zero W0 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_substfcT zero W0 _ _ _) ?_
      refine prf_congr_substfcT k0v k0s ?_
      exact prf_eq_trans (prf_substtc_binK_at T hT 0 W0 _ _) (prf_congr_binK k0a k0b)
    · refine prf_eq_trans (prf_substtc_binK_at T hT 0 W0 _ _) ?_
      refine prf_congr_binK k0a ?_
      exact prf_eq_trans (prf_substtc_gT _ zero W0 _ _ _) (prf_congr_gT _ k0v k0s k0b)
  have hchain : Prf (substfc zero W0 (substfc (numeral 1) W1 (substfc (numeral 2) W2
        (substfc (numeral 3) W3 (formCode AXATOM_BODY))))
      =eq eqCodeFn
        (substfcT (tcFn v) (tcFn s) (binK (termCode T) (tcFn a) (tcFn b)))
        (binK (termCode T) (tcFn a) (gT "substtsc" (tcFn v) (tcFn s) (tcFn b)))) :=
    prf_eq_trans (prf_congr_substfc_arg3
      (prf_eq_trans (prf_congr_substfc_arg3
        (prf_eq_trans (prf_congr_substfc_arg3 (prf_eq_trans hin0 hnorm3)) hmid2)) hmid1)) hout
  exact prf_mp (prf_provCode_congr hchain)
    (pcc_axiom_inst4 AXATOM_BODY (show ax_substfc_atom ∈ axioms by simp [axioms])
      (tcFn v) (tcFn s) (tcFn a) (tcFn b) (by hw_auto) (by hw_auto) (by hw_auto) (by hw_auto))

/-! ### §11.4 · Los DOS ensamblajes, en forma IMPLICACION -/

theorem caso_eq_core (v s a b : Term) :
    Prf (Formula.impl
      (land (targetSubsttc v s a) (targetSubsttc v s b))
      (targetSubstfc v s (cons (numeralM 4) (cons a (cons b nil))))) := by
  refine prf_deduction ?_
  have hh := prfH_hyp_self
    (land (targetSubsttc v s a) (targetSubsttc v s b))
  have hA : PrfH [land (targetSubsttc v s a) (targetSubsttc v s b)]
      (provFromCode (eqc (substtcT (tcFn v) (tcFn s) (tcFn a))
        (tcFn (substtc v s a)))) := PrfH_and_elim_left hh
  have hB : PrfH [land (targetSubsttc v s a) (targetSubsttc v s b)]
      (provFromCode (eqc (substtcT (tcFn v) (tcFn s) (tcFn b))
        (tcFn (substtc v s b)))) := PrfH_and_elim_right hh
  have iX0 : ∀ W, Prf (substtc zero W
        (substfcT (tcFn v) (tcFn s) (tcFn (cons (numeralM 4) (cons a (cons b nil)))))
      =eq substfcT (tcFn v) (tcFn s) (tcFn (cons (numeralM 4) (cons a (cons b nil))))) :=
    substtc_inv_substfcT (substtc_inv_tcFn v) (substtc_inv_tcFn s)
      (substtc_inv_tcFn (cons (numeralM 4) (cons a (cons b nil))))
  have iX1 : ∀ W, Prf (substtc zero W (substfcT (tcFn v) (tcFn s) (binT 4 (tcFn a) (tcFn b)))
      =eq substfcT (tcFn v) (tcFn s) (binT 4 (tcFn a) (tcFn b))) :=
    substtc_inv_substfcT (substtc_inv_tcFn v) (substtc_inv_tcFn s)
      (substtc_inv_binT (substtc_inv_tcFn a) (substtc_inv_tcFn b))
  have iX2 : ∀ W, Prf (substtc zero W (binT 4 (substtcT (tcFn v) (tcFn s) (tcFn a))
        (substtcT (tcFn v) (tcFn s) (tcFn b)))
      =eq binT 4 (substtcT (tcFn v) (tcFn s) (tcFn a))
        (substtcT (tcFn v) (tcFn s) (tcFn b))) :=
    substtc_inv_binT (invA v s a) (invA v s b)
  have iX3 : ∀ W, Prf (substtc zero W (binT 4 (tcFn (substtc v s a))
        (substtcT (tcFn v) (tcFn s) (tcFn b)))
      =eq binT 4 (tcFn (substtc v s a)) (substtcT (tcFn v) (tcFn s) (tcFn b))) :=
    substtc_inv_binT (substtc_inv_tcFn (substtc v s a)) (invA v s b)
  have iX4 : ∀ W, Prf (substtc zero W (binT 4 (tcFn (substtc v s a)) (tcFn (substtc v s b)))
      =eq binT 4 (tcFn (substtc v s a)) (tcFn (substtc v s b))) :=
    substtc_inv_binT (substtc_inv_tcFn (substtc v s a)) (substtc_inv_tcFn (substtc v s b))
  have h1 := prf_to_prfH (prf_mp (pcc_congr_substfcT_arg3_code (tcFn v) (tcFn s)
      (tcFn (cons (numeralM 4) (cons a (cons b nil)))) (binT 4 (tcFn a) (tcFn b))
      (substtc_inv_tcFn v) (substtc_inv_tcFn s)
      (substtc_inv_tcFn (cons (numeralM 4) (cons a (cons b nil)))))
    (pcc_dot_bin_symm 4 a b))
    [land (targetSubsttc v s a) (targetSubsttc v s b)]
  have h2 := prf_to_prfH (pcc_substfc_ter_dot (numeralM 4) "substtc"
      (fun c => liftTerm_numeralM c 4)
      (show ax_substfc_eq ∈ axioms by simp [axioms]) v s a b)
    [land (targetSubsttc v s a) (targetSubsttc v s b)]
  have h3 := PrfH.mp _ _ _ (prf_to_prfH (pcc_congr_binT_1_code 4
      (substtcT (tcFn v) (tcFn s) (tcFn b))
      (substtcT (tcFn v) (tcFn s) (tcFn a)) (tcFn (substtc v s a))
      (invA v s b) (invA v s a)) _) hA
  have h4 := PrfH.mp _ _ _ (prf_to_prfH (pcc_congr_binT_2_code 4 (tcFn (substtc v s a))
      (substtcT (tcFn v) (tcFn s) (tcFn b)) (tcFn (substtc v s b))
      (substtc_inv_tcFn (substtc v s a)) (invA v s b)) _) hB
  have h5 := prf_to_prfH (pcc_dot_bin 4 (substtc v s a) (substtc v s b))
    [land (targetSubsttc v s a) (targetSubsttc v s b)]
  have h6 := prf_to_prfH (prf_mp (prf_provCode_congr (prf_congr_eqCodeFn (prf_refl _)
      (prf_congr_tcFn (prf_eq_symm (prf_substfc_eq v s a b)))))
    (prf_provFromCode_eqCodeFn_refl
      (tcFn (cons (numeralM 4) (cons (substtc v s a) (cons (substtc v s b) nil))))))
    [land (targetSubsttc v s a) (targetSubsttc v s b)]
  refine PrfH_eq_trans_code _ _ _ iX0 h1
    (PrfH_eq_trans_code _ _ _ iX1 h2
      (PrfH_eq_trans_code _ _ _ iX2 h3
        (PrfH_eq_trans_code _ _ _ iX3 h4
          (PrfH_eq_trans_code _ _ _ iX4 h5 h6 ?_ ?_ ?_) ?_ ?_ ?_) ?_ ?_ ?_) ?_ ?_ ?_) ?_ ?_ ?_
    <;> hw_auto

theorem caso_atom_core (v s a b : Term) :
    Prf (Formula.impl (targetSubsttsc v s b)
      (targetSubstfc v s (cons (numeralM 3) (cons a (cons b nil))))) := by
  refine prf_deduction ?_
  have hB : PrfH [targetSubsttsc v s b]
      (provFromCode (eqc (substtscT (tcFn v) (tcFn s) (tcFn b))
        (tcFn (substtsc v s b)))) := prfH_hyp_self _
  have iX0 : ∀ W, Prf (substtc zero W
        (substfcT (tcFn v) (tcFn s) (tcFn (cons (numeralM 3) (cons a (cons b nil)))))
      =eq substfcT (tcFn v) (tcFn s) (tcFn (cons (numeralM 3) (cons a (cons b nil))))) :=
    substtc_inv_substfcT (substtc_inv_tcFn v) (substtc_inv_tcFn s)
      (substtc_inv_tcFn (cons (numeralM 3) (cons a (cons b nil))))
  have iX1 : ∀ W, Prf (substtc zero W (substfcT (tcFn v) (tcFn s) (binT 3 (tcFn a) (tcFn b)))
      =eq substfcT (tcFn v) (tcFn s) (binT 3 (tcFn a) (tcFn b))) :=
    substtc_inv_substfcT (substtc_inv_tcFn v) (substtc_inv_tcFn s)
      (substtc_inv_binT (substtc_inv_tcFn a) (substtc_inv_tcFn b))
  have iX2 : ∀ W, Prf (substtc zero W
        (binT 3 (tcFn a) (substtscT (tcFn v) (tcFn s) (tcFn b)))
      =eq binT 3 (tcFn a) (substtscT (tcFn v) (tcFn s) (tcFn b))) :=
    substtc_inv_binT (substtc_inv_tcFn a) (invAs v s b)
  have iX3 : ∀ W, Prf (substtc zero W (binT 3 (tcFn a) (tcFn (substtsc v s b)))
      =eq binT 3 (tcFn a) (tcFn (substtsc v s b))) :=
    substtc_inv_binT (substtc_inv_tcFn a) (substtc_inv_tcFn (substtsc v s b))
  have h1 := prf_to_prfH (prf_mp (pcc_congr_substfcT_arg3_code (tcFn v) (tcFn s)
      (tcFn (cons (numeralM 3) (cons a (cons b nil)))) (binT 3 (tcFn a) (tcFn b))
      (substtc_inv_tcFn v) (substtc_inv_tcFn s)
      (substtc_inv_tcFn (cons (numeralM 3) (cons a (cons b nil)))))
    (pcc_dot_bin_symm 3 a b)) [targetSubsttsc v s b]
  have h2 := prf_to_prfH (pcc_substfc_atom_dot v s a b) [targetSubsttsc v s b]
  have h3 := PrfH.mp _ _ _ (prf_to_prfH (pcc_congr_binT_2_code 3 (tcFn a)
      (substtscT (tcFn v) (tcFn s) (tcFn b)) (tcFn (substtsc v s b))
      (substtc_inv_tcFn a) (invAs v s b)) _) hB
  have h4 := prf_to_prfH (pcc_dot_bin 3 a (substtsc v s b)) [targetSubsttsc v s b]
  have h5 := prf_to_prfH (prf_mp (prf_provCode_congr (prf_congr_eqCodeFn (prf_refl _)
      (prf_congr_tcFn (prf_eq_symm (prf_substfc_atom v s a b)))))
    (prf_provFromCode_eqCodeFn_refl
      (tcFn (cons (numeralM 3) (cons a (cons (substtsc v s b) nil))))))
    [targetSubsttsc v s b]
  refine PrfH_eq_trans_code _ _ _ iX0 h1
    (PrfH_eq_trans_code _ _ _ iX1 h2
      (PrfH_eq_trans_code _ _ _ iX2 h3
        (PrfH_eq_trans_code _ _ _ iX3 h4 h5 ?_ ?_ ?_) ?_ ?_ ?_) ?_ ?_ ?_) ?_ ?_ ?_
    <;> hw_auto

/-! ### §11.5 · `CasoEq` y `CasoAtom`, DESCARGADOS -/

theorem casoEq : CasoEq := by
  intro wT v s X
  refine prf_deduction ?_
  have hh := prfH_hyp_self (land (wfAll1 wT) (land (shapeBin X 4)
    (land (In (nthc X (numeralM 1)) wT) (In (nthc X (numeralM 2)) wT))))
  have hwT := PrfH_and_elim_left hh
  have hR := PrfH_and_elim_right hh
  have hshape := PrfH_and_elim_left hR
  have hin1 := PrfH_and_elim_left (PrfH_and_elim_right hR)
  have hin2 := PrfH_and_elim_right (PrfH_and_elim_right hR)
  -- la evaluacion de TERMINO entra como LEMA EXTERNO sobre los DOS subcodigos
  have hTA := PrfH.mp _ _ _
    (prf_to_prfH (eval_substtc_imp wT v s (nthc X (numeralM 1))) _)
    (PrfH_and_intro hwT hin1)
  have hTB := PrfH.mp _ _ _
    (prf_to_prfH (eval_substtc_imp wT v s (nthc X (numeralM 2))) _)
    (PrfH_and_intro hwT hin2)
  have hC := PrfH.mp _ _ _
    (prf_to_prfH (caso_eq_core v s (nthc X (numeralM 1)) (nthc X (numeralM 2))) _)
    (PrfH_and_intro hTA hTB)
  exact PrfH_congr_targetSubstfc (PrfH_eq_symm hshape) hC

theorem casoAtom : CasoAtom := by
  intro wT v s X
  refine prf_deduction ?_
  have hh := prfH_hyp_self (land (wfAll1 wT) (land (shapeBin X 3)
    (argsIn wT (nthc X (numeralM 2)))))
  have hwT := PrfH_and_elim_left hh
  have hR := PrfH_and_elim_right hh
  have hshape := PrfH_and_elim_left hR
  have hargs := PrfH_and_elim_right hR
  have hTB := PrfH.mp _ _ _
    (prf_to_prfH (eval_substtsc_imp wT v s (nthc X (numeralM 2))) _)
    (PrfH_and_intro hwT hargs)
  have hC := PrfH.mp _ _ _
    (prf_to_prfH (caso_atom_core v s (nthc X (numeralM 1)) (nthc X (numeralM 2))) _) hTB
  exact PrfH_congr_targetSubstfc (PrfH_eq_symm hshape) hC

/-- **EL TEOREMA CON SIETE HIPOTESIS MENOS**: quedan SOLO `CasoUn 6` y `CasoUn 9`
    (`forallc` y `exc`), los DOS unicos constructores con `liftc` en el sustituyendo. -/
theorem pcc_eval_substfc_modulo_2 (h6 : CasoUn 6) (h9 : CasoUn 9)
    (wF wT v s f : Term) (hws : Prf (hasWit s)) (hfc : Prf (isFC1 wF wT f)) :
    Prf (provFromCode (eqc (substfcT (tcFn v) (tcFn s) (tcFn f)) (tcFn (substfc v s f)))) :=
  pcc_eval_substfc_modulo_8 casoBot casoAtom casoEq casoBin5 casoBin7 casoBin8 h6 h9
    casoHasWitLift wF wT v s f hws hfc

/-! ############################################################################
    ## §12 · DESCARGA de `CasoUn 6` (`forallc`) y `CasoUn 9` (`exc`).

    `paso2_caso_un_guarded` existe (`sondeos/SubstfcEx.lean:4307`) pero pide la HI
    como `Prf` CERRADA (`hIH : Prf (hasWit (liftc 0 s) ⇒ ...)`), y dentro del paso
    inductivo la HI llega como HIPOTESIS del contexto. Aqui va la MISMA prueba con la HI
    ya aplicada, como CONJUNTO de la premisa: `paso2_caso_un_conj`.
    ############################################################################ -/

/-- El DESCENSO de `liftc` (`ROBINSON_PlusPlus.Meta.EvalLiftcPrf.DESCENSO_hasWit`), en los simbolos de este fichero. -/
theorem DESCENSO_hasWit_local (s : Term) :
    Prf (Formula.impl (hasWit s)
      (provFromCode (eqc (liftcT (termCode zero) (tcFn s)) (tcFn (liftc zero s))))) :=
  ROBINSON_PlusPlus.Meta.EvalLiftcPrf.DESCENSO_hasWit s

/-- **`paso2_caso_un_guarded` con la HI como CONJUNTO** (no como `Prf` cerrada).
    Prueba identica a `sondeos/SubstfcEx.lean:4307`, salvo que `hIHg` se lee del contexto
    en vez de obtenerse por MP con `CRIT_hasWit_lift`. -/
theorem paso2_caso_un_conj (m : Nat) (hmem : forall_3 (AXBODY m) ∈ axioms)
    (hobj : ∀ v s a : Term,
      Prf (substfc v s (unc m a) =eq unc m (substfc (succ v) (liftc zero s) a)))
    (v s f : Term) :
    Prf (Formula.impl (land (hasWit s) (targetSubstfc (succ v) (liftc zero s) f))
      (targetSubstfc v s (unc m f))) := by
  refine prf_deduction ?_
  have hh := prfH_hyp_self (land (hasWit s) (targetSubstfc (succ v) (liftc zero s) f))
  have hg : PrfH [land (hasWit s) (targetSubstfc (succ v) (liftc zero s) f)] (hasWit s) :=
    PrfH_and_elim_left hh
  have hIHg : PrfH [land (hasWit s) (targetSubstfc (succ v) (liftc zero s) f)]
      (provFromCode (eqc (substfcT (tcFn (succ v)) (tcFn (liftc zero s)) (tcFn f))
        (tcFn (substfc (succ v) (liftc zero s) f)))) := PrfH_and_elim_right hh
  have hLift : PrfH [land (hasWit s) (targetSubstfc (succ v) (liftc zero s) f)]
      (provFromCode (eqc (liftcT (termCode zero) (tcFn s)) (tcFn (liftc zero s)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (DESCENSO_hasWit_local s) _) hg
  have iz : ∀ W, Prf (substtc zero W (termCode zero) =eq termCode zero) :=
    fun W => prf_substtc_termCode_zero 0 W
  have iL : ∀ W, Prf (substtc zero W (liftcT (termCode zero) (tcFn s))
      =eq liftcT (termCode zero) (tcFn s)) :=
    substtc_inv_liftcT iz (substtc_inv_tcFn s)
  have iA : ∀ W, Prf (substtc zero W (substfcT (tcFn v) (tcFn s) (tcFn (unc m f)))
      =eq substfcT (tcFn v) (tcFn s) (tcFn (unc m f))) :=
    substtc_inv_substfcT (substtc_inv_tcFn v) (substtc_inv_tcFn s)
      (substtc_inv_tcFn (unc m f))
  have h1 : Prf (provFromCode (eqc (substfcT (tcFn v) (tcFn s) (tcFn (unc m f)))
      (unT m (substfcT (succcT (tcFn v)) (liftcT (termCode zero) (tcFn s)) (tcFn f))))) :=
    fuego_ab_un m hmem v s f
  have h2 : PrfH [land (hasWit s) (targetSubstfc (succ v) (liftc zero s) f)]
      (provFromCode (eqc
        (substfcT (tcFn v) (tcFn s) (tcFn (unc m f)))
        (unT m (substfcT (tcFn (succ v)) (liftcT (termCode zero) (tcFn s)) (tcFn f))))) :=
    prf_to_prfH (prf_mp (prf_provCode_congr (prf_congr_eqCodeFn (prf_refl _)
      (prf_congr_unT (prf_congr_substfcT (prf_eq_symm (prf_tc_succ' v))
        (prf_refl _) (prf_refl _))))) h1) _
  have h3 : PrfH [land (hasWit s) (targetSubstfc (succ v) (liftc zero s) f)]
      (provFromCode (eqc
        (unT m (substfcT (tcFn (succ v)) (liftcT (termCode zero) (tcFn s)) (tcFn f)))
        (unT m (substfcT (tcFn (succ v)) (tcFn (liftc zero s)) (tcFn f))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_congr_unT_code m _ _
      (substtc_inv_substfcT (substtc_inv_tcFn (succ v)) iL (substtc_inv_tcFn f))) _)
      (PrfH.mp _ _ _ (prf_to_prfH (pcc_congr_substfcT_arg2_code (tcFn (succ v)) (tcFn f)
        (liftcT (termCode zero) (tcFn s)) (tcFn (liftc zero s))
        (substtc_inv_tcFn (succ v)) (substtc_inv_tcFn f) iL) _) hLift)
  have h4 : PrfH [land (hasWit s) (targetSubstfc (succ v) (liftc zero s) f)]
      (provFromCode (eqc
        (unT m (substfcT (tcFn (succ v)) (tcFn (liftc zero s)) (tcFn f)))
        (unT m (tcFn (substfc (succ v) (liftc zero s) f))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_congr_unT_code m _ _
      (substtc_inv_substfcT (substtc_inv_tcFn (succ v)) (substtc_inv_tcFn (liftc zero s))
        (substtc_inv_tcFn f))) _) hIHg
  have h5 : PrfH [land (hasWit s) (targetSubstfc (succ v) (liftc zero s) f)]
      (provFromCode (eqc
        (unT m (tcFn (substfc (succ v) (liftc zero s) f)))
        (tcFn (unc m (substfc (succ v) (liftc zero s) f))))) :=
    prf_to_prfH (pcc_dot_un m (substfc (succ v) (liftc zero s) f)) _
  have h6 : PrfH [land (hasWit s) (targetSubstfc (succ v) (liftc zero s) f)]
      (provFromCode (eqc
        (tcFn (unc m (substfc (succ v) (liftc zero s) f)))
        (tcFn (substfc v s (unc m f))))) :=
    prf_to_prfH (prf_mp (prf_provCode_congr (prf_congr_eqCodeFn (prf_refl _)
      (prf_congr_tcFn (prf_eq_symm (hobj v s f)))))
      (prf_provFromCode_eqCodeFn_refl
        (tcFn (unc m (substfc (succ v) (liftc zero s) f))))) _
  refine PrfH_eq_trans_code _ _ _ iA h2
    (PrfH_eq_trans_code _ _ _
      (substtc_inv_unT (substtc_inv_substfcT (substtc_inv_tcFn (succ v)) iL
        (substtc_inv_tcFn f)))
      h3
      (PrfH_eq_trans_code _ _ _
        (substtc_inv_unT (substtc_inv_substfcT (substtc_inv_tcFn (succ v))
          (substtc_inv_tcFn (liftc zero s)) (substtc_inv_tcFn f)))
        h4
        (PrfH_eq_trans_code _ _ _
          (substtc_inv_unT (substtc_inv_tcFn (substfc (succ v) (liftc zero s) f)))
          h5 h6 ?_ ?_ ?_) ?_ ?_ ?_) ?_ ?_ ?_) ?_ ?_ ?_
    <;> hw_auto

/-- **`CasoUn m` DESCARGADO**, generico en el tag. -/
theorem casoUn_gen (m : Nat) (hmem : forall_3 (AXBODY m) ∈ axioms)
    (hobj : ∀ v s a : Term,
      Prf (substfc v s (unc m a) =eq unc m (substfc (succ v) (liftc zero s) a))) :
    CasoUn m := by
  intro v s X
  refine prf_deduction ?_
  have hh := prfH_hyp_self (land (hasWit s) (land (shapeUn X m)
    (targetSubstfc (succ v) (liftc zero s) (nthc X (numeralM 1)))))
  have hws := PrfH_and_elim_left hh
  have hR := PrfH_and_elim_right hh
  have hshape := PrfH_and_elim_left hR
  have hIH := PrfH_and_elim_right hR
  have hC := PrfH.mp _ _ _
    (prf_to_prfH (paso2_caso_un_conj m hmem hobj v s (nthc X (numeralM 1))) _)
    (PrfH_and_intro hws hIH)
  exact PrfH_congr_targetSubstfc (PrfH_eq_symm hshape) hC

theorem casoUn6 : CasoUn 6 := casoUn_gen 6 mem6 prf_substfc_forall
theorem casoUn9 : CasoUn 9 := casoUn_gen 9 mem9 prf_substfc_ex

/-! ############################################################################
    ## §13 · **`pcc_eval_substfc` — SIN NINGUNA HIPOTESIS**
    ############################################################################ -/

/-- **EL DESCENSO COMPLETO**, sin hipotesis colgando. -/
theorem DESCENSO_substfc (wF wT v s t : Term) :
    Prf (Formula.impl (GUARD wF wT s t) (targetSubstfc v s t)) :=
  DESCENSO_substfc_imp casoBot casoAtom casoEq casoBin5 casoBin7 casoBin8 casoUn6 casoUn9
    casoHasWitLift wF wT v s t

/-- **★ `pcc_eval_substfc` ★** — la evaluacion PROVABLE de `substfc` con `v`, `s`, `f`
    **ABSTRACTOS**, guardada por los DOS testigos (formula `wF` y termino `wT`).
    CERO axiomas de Lean, cero `sorry`, cero hipotesis. -/
theorem pcc_eval_substfc (wF wT v s f : Term)
    (hws : Prf (hasWit s)) (hfc : Prf (isFC1 wF wT f)) :
    Prf (provFromCode (eqc (substfcT (tcFn v) (tcFn s) (tcFn f)) (tcFn (substfc v s f)))) :=
  prf_mp (DESCENSO_substfc wF wT v s f) (prf_and_intro hws hfc)

/-! ############################################################################
    ## §14 · CONTROLES DE DISCRIMINACION — el reconocedor de FORMULA no acepta
       codigos de TERMINO. La forma ECUACIONAL FORTALECE la posicional
       `isFormCodeB2`, y la discriminacion de aquella se hereda entera.
    ############################################################################ -/

/-! ############################################################################
    ## §15 · LA FORMA CON LOS TESTIGOS CUANTIFICADOS — la que llega rio abajo.
    ############################################################################ -/

/-- **`pcc_eval_substfc` con los DOS testigos CUANTIFICADOS** (la forma que consume
    el reflector rio abajo: ninguna lista testigo aparece en el enunciado). -/
theorem pcc_eval_substfc_wit (v s f : Term) :
    Prf (Formula.impl (land (hasWit s) (hasWitF f)) (targetSubstfc v s f)) := by
  refine prf_deduction ?_
  have hh := prfH_hyp_self (land (hasWit s) (hasWitF f))
  have hwf : PrfH [land (hasWit s) (hasWitF f)]
      (Formula.ex (Formula.ex (isFC1 (.var 1) (.var 0) (liftTerm 0 (liftTerm 0 f))))) :=
    PrfH_and_elim_right hh
  refine PrfH_ex_elim hwf ?_
  rw [liftF_targetSubstfc]
  refine PrfH_ex_elim (PrfH.hyp _ _ (List.Mem.head _)) ?_
  rw [liftF_targetSubstfc]
  refine PrfH.mp _ _ _
    (prf_to_prfH (DESCENSO_substfc (.var 1) (.var 0)
      (liftTerm 0 (liftTerm 0 v)) (liftTerm 0 (liftTerm 0 s))
      (liftTerm 0 (liftTerm 0 f))) _)
    (PrfH_and_intro ?_ ?_)
  · rw [← liftF_hasWit, ← liftF_hasWit]
    exact PrfH_and_elim_left
      (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
  · exact PrfH.hyp _ _ (List.Mem.head _)

/-! ### CONTROLES NEGATIVOS -/

set_option linter.unusedVariables false in
/-- El objetivo NO es una reflexividad disfrazada. -/
example (v s f : Term) : True := by
  fail_if_success
    exact (rfl : substfcT (tcFn v) (tcFn s) (tcFn f) = tcFn (substfc v s f))
  trivial

/-- El predicado de FORMULA NO es el de TERMINO con las listas fusionadas. -/
example (wF wT X : Term) : True := by
  fail_if_success exact (rfl : isFormCodeE2 wF wT X = isTermCodeE1 wT X)
  trivial

/-- La guarda de FORMULA lleva DENTRO la guarda de TERMINO que pide `pcc_eval_substtc'`
    — la mitad `wfAll1 wT` es LITERALMENTE la de `sondeos/EvalSubsttc.lean`. -/
example (wF wT c : Term) :
    isFC1 wF wT c = land (land (wfAll1 wT) (wfAllF wF wT)) (In c wF) := rfl

/-- Y de la guarda de FORMULA sale, por `rfl`, el `isTC1` que consume `pcc_eval_substtc'`
    en cuanto se tiene la pertenencia del SUBcodigo a `wT`. -/
example (wT z : Term) : isTC1 wT z = land (wfAll1 wT) (In z wT) := rfl

end ROBINSON_PlusPlus.Meta.EvalSubstfcPrf

/-! ## `export` — por PROPÓSITO DECLARADO, y dicho como tal

⚠️ Aquí **no** se puede exportar «por consumo» (§17) como se hizo en B3.2, y conviene dejarlo
escrito en vez de fingir una medición: medido con el filtro correcto —descontando los nombres
que el propio fichero declara—, **ningún** sondeo consume nada de este módulo. Los que parecían
consumirlo (`HasWitFReal.lean`, `EnsamblajeTriple.lean`, `EnsamblajeMedida.lean`,
`SubstfcEx.lean`) son **variantes del mismo trabajo**: declaran ellos mismos los nombres que
usan. Consumo de una copia no es consumo.

Se exporta, entonces, la **API frontal**: los dos teoremas del encargo, ⭐ el **chasis
genérico** `pcc_eval_substfc_modulo_8` —el teorema parametrizado sobre los ocho casos, que es
lo que querría quien tenga que enmendar uno—, el objetivo
`targetSubstfc` con su fontanería De Bruijn (que es lo que un reflector necesita para moverlo
bajo `substFormula`/`liftFormula`), el descenso, y el constructor unario genérico en el tag con
sus dos pertenencias. Todo lo demás —los ocho casos, sus ramas, el predicado de la inducción y
su escalera `psi`— se queda dentro del namespace hasta que alguien lo pida. Los tres
`pcc_eval_substfc_modulo_5`/`_4`/`_2` se quedan también: son los **hitos** del camino
incremental (el teorema con 5, 4 y 2 hipótesis abiertas), y documentan la ruta que siguió la
prueba, pero ya no tienen consumidor porque el teorema completo existe.

⭐ El consumidor previsto es **C3**: el antecedente de `pcc_eval_substfc_wit` es literalmente el
conjunto extra que ADR‑020 metió dentro del `⇔` de los 7 esquemas (ver `Meta/LineWFGuardPrf.lean`
§2), así que con este módulo el reflector `hCarc` pasa a ser una MP. -/
export ROBINSON_PlusPlus.Meta.EvalSubstfcPrf (
  pcc_eval_substfc pcc_eval_substfc_wit DESCENSO_substfc pcc_eval_substfc_modulo_8
  targetSubstfc liftF_targetSubstfc substF_targetSubstfc
  PrfH_congr_targetSubstfc substF_hole_fc
  unc AXBODY mem6 mem9 pcc_substfc_un_dot fuego_ab_un
  substCodeT_unc substCodeF_AXBODY pcc_congr_substfcT_arg2_code
  CasoBot CasoBin CasoUn CasoEq CasoAtom HasWitLift
)

/-! ## FOOTPRINT — la única auditoría que vale -/

#print axioms ROBINSON_PlusPlus.Meta.EvalSubstfcPrf.pcc_eval_substfc
#print axioms ROBINSON_PlusPlus.Meta.EvalSubstfcPrf.pcc_eval_substfc_wit
#print axioms ROBINSON_PlusPlus.Meta.EvalSubstfcPrf.DESCENSO_substfc
#print axioms ROBINSON_PlusPlus.Meta.EvalSubstfcPrf.pcc_substfc_un_dot
#print axioms ROBINSON_PlusPlus.Meta.EvalSubstfcPrf.pcc_congr_substfcT_arg2_code

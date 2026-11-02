/- # `sondeos/CongruenciaHueco.lean` — UN genérico para las 19 congruencias internas `pcc_congr_*_code`

   Re‑medición en T48 (2026‑11‑02) de `pcc_congr_hole_code`, el genérico de
   `Probe/B3_planos_dedup_kit.lean` y `Probe/B3_planos_dedup.lean` (2026‑09‑04), que el triaje del
   2026‑09‑11 mandó promover y nunca se promovió.

   ⚠️ **ADAPTADO, no copiado.** El original no compila contra el build de hoy: desde la guarda de
   testigo, `PrfH_leibniz_apply` (y `pcc_leibniz_code`, debajo) piden `hasWitF` del contexto y
   `hasWit` de los dos extremos. El genérico gana cuatro hipótesis (`hwFX`, `hwF0`, `hwX`, `hwY`) y va
   por `pcc_leibniz_apply_imp` (`Meta/EvalArithPrf.lean`) en vez de `PrfH_leibniz_apply`
   (`Meta/EvalCarcNthcPrf.lean`): así sólo usa lo que hay en `EvalArithPrf` y aguas arriba, y
   `EvalArithPrf` está en la clausura de imports de los DOCE módulos que tienen copia (medido sobre
   las líneas `import`). El sitio que se probó en 2026‑09 —`Meta/CodeCtorKit.lean`— ya no basta:
   `EvalArithPrf`, `EvalCarcNthcPrf`, `EvalMulPrf` y `LineWFTrackedPrf` no lo importan.

   Qué se mide:
     §1 — el genérico, con la guarda.
     §2 — las 19 copias del build, como corolarios del genérico, con su enunciado LITERAL (firma
          copiada, auto‑parámetros `hw_auto` incluidos); y para cada una, `@corolario = @original`
          por `rfl`: si la copia de la firma no fuera la del build, no tiparía.
     §3 — controles negativos.

   CERO axiomas nuevos, CERO `sorry`. No es un módulo del build y no cambia ninguno. -/
import ROBINSON_PlusPlus.Meta

open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.TcArithPrf ROBINSON_PlusPlus.Meta.Sigma1Prf
open ROBINSON_PlusPlus.Meta.Sigma1AtomPrf ROBINSON_PlusPlus.Meta.MpCodePrf
open ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf ROBINSON_PlusPlus.Meta.NumCodeClosedPrf
open ROBINSON_PlusPlus.Meta.EvalArithPrf ROBINSON_PlusPlus.Meta.EvalLtPrf
open ROBINSON_PlusPlus.Meta.NatArithPrf ROBINSON_PlusPlus.Meta.DotConsPrf
open ROBINSON_PlusPlus.Meta.DerivCondPrf ROBINSON_PlusPlus.Meta.CodeCtorKit
open ROBINSON_PlusPlus.Meta.HilbertDeduction ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf ROBINSON_PlusPlus.Meta.TrackedCorePrf
open ROBINSON_PlusPlus.Meta.LineWFTrackedPrf ROBINSON_PlusPlus.Meta.EvalRunFnPrf
open ROBINSON_PlusPlus.Meta.EvalListPrf ROBINSON_PlusPlus.Meta.EvalNthcPrf
open ROBINSON_PlusPlus.Meta.EvalPredPrf ROBINSON_PlusPlus.Meta.EvalMulPrf
open ROBINSON_PlusPlus.Meta.EvalLiftfcPrf ROBINSON_PlusPlus.Meta.EvalSubstfcPrf
open ROBINSON_PlusPlus.Meta.EvalSubsttcPrf ROBINSON_PlusPlus.Meta.LiftcCodePrf
open ROBINSON_PlusPlus.Meta.SubstfcCodePrf ROBINSON_PlusPlus.Meta.TrackedAtomsPrf

set_option maxHeartbeats 1000000

namespace CongruenciaHueco

/-! ## §1 · EL GENÉRICO

    El contexto entra como `F : Term → Term`. Las dos obligaciones de estructura (`hinv`, `hhole`)
    son las que cada copia descarga a mano; las cuatro de testigo, las que pide hoy Leibniz. -/

theorem pcc_congr_hole_code (F : Term → Term) (X Y : Term)
    (hinv : ∀ W, Prf (substtc zero W (F X) =eq F X))
    (hhole : ∀ w, Prf (substtc zero w (F (varc (numeral 0))) =eq F w))
    (hwFX : Prf (hasWit (F X))) (hwF0 : Prf (hasWit (F (varc (numeral 0)))))
    (hwX : Prf (hasWit X)) (hwY : Prf (hasWit Y)) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (F X) (F Y))) := by
  let Ac : Term := eqc (F X) (F (varc (numeral 0)))
  have hcomp : ∀ w : Term, Prf (substfc zero w Ac =eq eqc (F X) (F w)) := by
    intro w
    refine prf_eq_trans (prf_substfc_eq zero w (F X) (F (varc (numeral 0)))) ?_
    exact prf_congr_eqCodeFn (hinv w) (hhole w)
  have hAX : Prf (provFromCode (substfc zero X Ac)) :=
    prf_mp (prf_provCode_congr (prf_eq_symm (hcomp X)))
      (prf_provFromCode_eqCodeFn_refl (F X))
  have himp : Prf (provFromCode (eqc X Y) ⇒ provFromCode (substfc zero Y Ac)) :=
    pcc_leibniz_apply_imp Ac X Y
      (prf_hasWitF_eq2 (F X) (F (varc (numeral 0))) hwFX hwF0) hwX hwY hAX
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcomp Y)) _)
    (PrfH.mp _ _ _ (prf_to_prfH himp _) (prfH_hyp_self _))

/-! ## §2 · LAS 19 COPIAS DEL BUILD, como corolarios (enunciado LITERAL)

    Orden: el de `git grep -n "^theorem pcc_congr_"` sobre `ROBINSON_PlusPlus/`. -/

/-! ### `Meta/CodeCtorKit.lean` (3) -/

theorem C_pcc_congr_binT_2_code (m : Nat) (A X Y : Term)
    (hA : ∀ W, Prf (substtc zero W A =eq A)) (hX : ∀ W, Prf (substtc zero W X =eq X))
    (hwA : Prf (hasWit A) := by hw_auto) (hwX : Prf (hasWit X) := by hw_auto)
    (hwY : Prf (hasWit Y) := by hw_auto) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (binT m A X) (binT m A Y))) :=
  pcc_congr_hole_code (fun s => binT m A s) X Y
    (fun W => prf_eq_trans (prf_substtc_binT m W A X) (prf_congr_binT (hA W) (hX W)))
    (fun w => prf_eq_trans (prf_substtc_binT m w A (varc (numeral 0)))
      (prf_congr_binT (hA w) (prf_substtc_varc0 w)))
    (prf_hasWit_binT m hwA hwX) (prf_hasWit_binT m hwA (prf_hasWit_varc (numeral 0))) hwX hwY

theorem C_pcc_congr_binT_1_code (m : Nat) (B X Y : Term)
    (hB : ∀ W, Prf (substtc zero W B =eq B)) (hX : ∀ W, Prf (substtc zero W X =eq X))
    (hwB : Prf (hasWit B) := by hw_auto) (hwX : Prf (hasWit X) := by hw_auto)
    (hwY : Prf (hasWit Y) := by hw_auto) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (binT m X B) (binT m Y B))) :=
  pcc_congr_hole_code (fun s => binT m s B) X Y
    (fun W => prf_eq_trans (prf_substtc_binT m W X B) (prf_congr_binT (hX W) (hB W)))
    (fun w => prf_eq_trans (prf_substtc_binT m w (varc (numeral 0)) B)
      (prf_congr_binT (prf_substtc_varc0 w) (hB w)))
    (prf_hasWit_binT m hwX hwB) (prf_hasWit_binT m (prf_hasWit_varc (numeral 0)) hwB) hwX hwY

theorem C_pcc_congr_unT_code (m : Nat) (X Y : Term)
    (hX : ∀ W, Prf (substtc zero W X =eq X))
    (hwX : Prf (hasWit X) := by hw_auto) (hwY : Prf (hasWit Y) := by hw_auto) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (unT m X) (unT m Y))) :=
  pcc_congr_hole_code (fun s => unT m s) X Y
    (fun W => prf_eq_trans (prf_substtc_unT m W X) (prf_congr_unT (hX W)))
    (fun w => prf_eq_trans (prf_substtc_unT m w (varc (numeral 0)))
      (prf_congr_unT (prf_substtc_varc0 w)))
    (prf_hasWit_unT m hwX) (prf_hasWit_unT m (prf_hasWit_varc (numeral 0))) hwX hwY

/-! ### `Meta/EvalArithPrf.lean` (2; la primera, en forma de REGLA) -/

theorem C_pcc_congr_succ_code (X Y : Term) (hX : ∀ W, Prf (substtc zero W X =eq X))
    (hwX : Prf (hasWit X)) (hwY : Prf (hasWit Y))
    (heq : Prf (provFromCode (eqc X Y))) :
    Prf (provFromCode (eqc (succcT X) (succcT Y))) :=
  prf_mp (pcc_congr_hole_code succcT X Y
    (fun W => prf_eq_trans (prf_substtc_succcT zero W X) (prf_congr_succcT (hX W)))
    (fun w => prf_eq_trans (prf_substtc_succcT zero w (varc (numeral 0)))
      (prf_congr_succcT (prf_substtc_varc0 w)))
    (prf_hasWit_succcT hwX) (prf_hasWit_succcT (prf_hasWit_varc (numeral 0))) hwX hwY) heq

theorem C_pcc_congr_succ_code_imp (X Y : Term) (hX : ∀ W, Prf (substtc zero W X =eq X))
    (hwX : Prf (hasWit X)) (hwY : Prf (hasWit Y)) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (succcT X) (succcT Y))) :=
  pcc_congr_hole_code succcT X Y
    (fun W => prf_eq_trans (prf_substtc_succcT zero W X) (prf_congr_succcT (hX W)))
    (fun w => prf_eq_trans (prf_substtc_succcT zero w (varc (numeral 0)))
      (prf_congr_succcT (prf_substtc_varc0 w)))
    (prf_hasWit_succcT hwX) (prf_hasWit_succcT (prf_hasWit_varc (numeral 0))) hwX hwY

/-! ### `Meta/EvalCarcNthcPrf.lean` (1) -/

theorem C_pcc_congr_carcT_code_imp (X Y : Term) (hX : ∀ W, Prf (substtc zero W X =eq X))
    (hwX : Prf (hasWit X)) (hwY : Prf (hasWit Y)) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (carcT X) (carcT Y))) :=
  pcc_congr_hole_code carcT X Y
    (fun W => prf_eq_trans (prf_substtc_carcT zero W X) (prf_congr_carcT (hX W)))
    (fun w => prf_eq_trans (prf_substtc_carcT zero w (varc (numeral 0)))
      (prf_congr_carcT (prf_substtc_varc0 w)))
    (prf_hasWit_carcT hwX) (prf_hasWit_carcT (prf_hasWit_varc (numeral 0))) hwX hwY

/-! ### `Meta/EvalLiftfcPrf.lean` (1) -/

theorem C_pcc_congr_liftfcT_arg2_code (A X Y : Term)
    (hA : ∀ W, Prf (substtc zero W A =eq A)) (hX : ∀ W, Prf (substtc zero W X =eq X))
    (hwA : Prf (hasWit A) := by hw_auto) (hwX : Prf (hasWit X) := by hw_auto)
    (hwY : Prf (hasWit Y) := by hw_auto) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (liftfcT A X) (liftfcT A Y))) :=
  pcc_congr_hole_code (fun s => liftfcT A s) X Y
    (fun W => prf_eq_trans (prf_substtc_liftfcT zero W A X) (prf_congr_liftfcT (hA W) (hX W)))
    (fun w => prf_eq_trans (prf_substtc_liftfcT zero w A (varc (numeral 0)))
      (prf_congr_liftfcT (hA w) (prf_substtc_varc0 w)))
    (prf_hasWit_liftfcT hwA hwX) (prf_hasWit_liftfcT hwA (prf_hasWit_varc (numeral 0))) hwX hwY

/-! ### `Meta/EvalMulPrf.lean` (1) -/

theorem C_pcc_congr_addcT1_code_imp (X Y A : Term)
    (hX : ∀ W, Prf (substtc zero W X =eq X)) (hA : ∀ W, Prf (substtc zero W A =eq A))
    (hwX : Prf (hasWit X)) (hwY : Prf (hasWit Y)) (hwA : Prf (hasWit A)) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (addcT X A) (addcT Y A))) :=
  pcc_congr_hole_code (fun s => addcT s A) X Y
    (fun W => prf_eq_trans (prf_substtc_addcT zero W X A) (prf_congr_addcT (hX W) (hA W)))
    (fun w => prf_eq_trans (prf_substtc_addcT zero w (varc (numeral 0)) A)
      (prf_congr_addcT (prf_substtc_varc0 w) (hA w)))
    (prf_hasWit_addcT hwX hwA) (prf_hasWit_addcT (prf_hasWit_varc (numeral 0)) hwA) hwX hwY

/-! ### `Meta/EvalPredPrf.lean` (1, en forma de REGLA) -/

theorem C_pcc_congr_predcT_code (X Y : Term) (hX : ∀ W, Prf (substtc zero W X =eq X))
    (hwX : Prf (hasWit X)) (hwY : Prf (hasWit Y))
    (heq : Prf (provFromCode (eqc X Y))) :
    Prf (provFromCode (eqc (predcT X) (predcT Y))) :=
  prf_mp (pcc_congr_hole_code predcT X Y
    (fun W => prf_eq_trans (prf_substtc_predcT zero W X) (prf_congr_predcT (hX W)))
    (fun w => prf_eq_trans (prf_substtc_predcT zero w (varc (numeral 0)))
      (prf_congr_predcT (prf_substtc_varc0 w)))
    (prf_hasWit_predcT hwX) (prf_hasWit_predcT (prf_hasWit_varc (numeral 0))) hwX hwY) heq

/-! ### `Meta/EvalSubstfcPrf.lean` (1) -/

theorem C_pcc_congr_substfcT_arg2_code (A C X Y : Term)
    (hA : ∀ W, Prf (substtc zero W A =eq A)) (hC : ∀ W, Prf (substtc zero W C =eq C))
    (hX : ∀ W, Prf (substtc zero W X =eq X))
    (hwA : Prf (hasWit A) := by hw_auto) (hwC : Prf (hasWit C) := by hw_auto)
    (hwX : Prf (hasWit X) := by hw_auto) (hwY : Prf (hasWit Y) := by hw_auto) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (substfcT A X C) (substfcT A Y C))) :=
  pcc_congr_hole_code (fun s => substfcT A s C) X Y
    (fun W => prf_eq_trans (prf_substtc_substfcT zero W A X C)
      (prf_congr_substfcT (hA W) (hX W) (hC W)))
    (fun w => prf_eq_trans (prf_substtc_substfcT zero w A (varc (numeral 0)) C)
      (prf_congr_substfcT (hA w) (prf_substtc_varc0 w) (hC w)))
    (prf_hasWit_funcc3 (strCode sym!"substfc") A X C hwA hwX hwC)
    (prf_hasWit_funcc3 (strCode sym!"substfc") A (varc (numeral 0)) C hwA
      (prf_hasWit_varc (numeral 0)) hwC) hwX hwY

/-! ### `Meta/EvalSubsttcPrf.lean` (2) -/

theorem C_pcc_congr_substtcT_arg3_code (A B X Y : Term)
    (hA : ∀ W, Prf (substtc zero W A =eq A)) (hB : ∀ W, Prf (substtc zero W B =eq B))
    (hX : ∀ W, Prf (substtc zero W X =eq X))
    (hwA : Prf (hasWit A) := by hw_auto) (hwB : Prf (hasWit B) := by hw_auto)
    (hwX : Prf (hasWit X) := by hw_auto) (hwY : Prf (hasWit Y) := by hw_auto) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (substtcT A B X) (substtcT A B Y))) :=
  pcc_congr_hole_code (fun s => substtcT A B s) X Y
    (fun W => prf_eq_trans (prf_substtc_substtcT zero W A B X)
      (prf_congr_substtcT (hA W) (hB W) (hX W)))
    (fun w => prf_eq_trans (prf_substtc_substtcT zero w A B (varc (numeral 0)))
      (prf_congr_substtcT (hA w) (hB w) (prf_substtc_varc0 w)))
    (prf_hasWit_funcc3 (strCode sym!"substtc") A B X hwA hwB hwX)
    (prf_hasWit_funcc3 (strCode sym!"substtc") A B (varc (numeral 0)) hwA hwB
      (prf_hasWit_varc (numeral 0))) hwX hwY

theorem C_pcc_congr_substtscT_arg3_code (A B X Y : Term)
    (hA : ∀ W, Prf (substtc zero W A =eq A)) (hB : ∀ W, Prf (substtc zero W B =eq B))
    (hX : ∀ W, Prf (substtc zero W X =eq X))
    (hwA : Prf (hasWit A) := by hw_auto) (hwB : Prf (hasWit B) := by hw_auto)
    (hwX : Prf (hasWit X) := by hw_auto) (hwY : Prf (hasWit Y) := by hw_auto) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (substtscT A B X) (substtscT A B Y))) :=
  pcc_congr_hole_code (fun s => substtscT A B s) X Y
    (fun W => prf_eq_trans (prf_substtc_substtscT zero W A B X)
      (prf_congr_substtscT (hA W) (hB W) (hX W)))
    (fun w => prf_eq_trans (prf_substtc_substtscT zero w A B (varc (numeral 0)))
      (prf_congr_substtscT (hA w) (hB w) (prf_substtc_varc0 w)))
    (prf_hasWit_funcc3 (strCode sym!"substtsc") A B X hwA hwB hwX)
    (prf_hasWit_funcc3 (strCode sym!"substtsc") A B (varc (numeral 0)) hwA hwB
      (prf_hasWit_varc (numeral 0))) hwX hwY

/-! ### `Meta/LiftcCodePrf.lean` (4) -/

theorem C_pcc_congr_liftcT_arg2_code (A X Y : Term)
    (hA : ∀ W, Prf (substtc zero W A =eq A)) (hX : ∀ W, Prf (substtc zero W X =eq X))
    (hwA : Prf (hasWit A) := by hw_auto) (hwX : Prf (hasWit X) := by hw_auto)
    (hwY : Prf (hasWit Y) := by hw_auto) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (liftcT A X) (liftcT A Y))) :=
  pcc_congr_hole_code (fun s => liftcT A s) X Y
    (fun W => prf_eq_trans (prf_substtc_liftcT zero W A X) (prf_congr_liftcT (hA W) (hX W)))
    (fun w => prf_eq_trans (prf_substtc_liftcT zero w A (varc (numeral 0)))
      (prf_congr_liftcT (hA w) (prf_substtc_varc0 w)))
    (prf_hasWit_liftcT hwA hwX) (prf_hasWit_liftcT hwA (prf_hasWit_varc (numeral 0))) hwX hwY

theorem C_pcc_congr_liftscT_arg2_code (A X Y : Term)
    (hA : ∀ W, Prf (substtc zero W A =eq A)) (hX : ∀ W, Prf (substtc zero W X =eq X))
    (hwA : Prf (hasWit A) := by hw_auto) (hwX : Prf (hasWit X) := by hw_auto)
    (hwY : Prf (hasWit Y) := by hw_auto) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (liftscT A X) (liftscT A Y))) :=
  pcc_congr_hole_code (fun s => liftscT A s) X Y
    (fun W => prf_eq_trans (prf_substtc_liftscT zero W A X) (prf_congr_liftscT (hA W) (hX W)))
    (fun w => prf_eq_trans (prf_substtc_liftscT zero w A (varc (numeral 0)))
      (prf_congr_liftscT (hA w) (prf_substtc_varc0 w)))
    (prf_hasWit_liftscT hwA hwX) (prf_hasWit_liftscT hwA (prf_hasWit_varc (numeral 0))) hwX hwY

theorem C_pcc_congr_consT_arg2_code (A X Y : Term)
    (hA : ∀ W, Prf (substtc zero W A =eq A)) (hX : ∀ W, Prf (substtc zero W X =eq X))
    (hwA : Prf (hasWit A) := by hw_auto) (hwX : Prf (hasWit X) := by hw_auto)
    (hwY : Prf (hasWit Y) := by hw_auto) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (consT A X) (consT A Y))) :=
  pcc_congr_hole_code (fun s => consT A s) X Y
    (fun W => prf_eq_trans (prf_substtc_consT zero W A X) (prf_congr_consT (hA W) (hX W)))
    (fun w => prf_eq_trans (prf_substtc_consT zero w A (varc (numeral 0)))
      (prf_congr_consT (hA w) (prf_substtc_varc0 w)))
    (prf_hasWit_consT hwA hwX) (prf_hasWit_consT hwA (prf_hasWit_varc (numeral 0))) hwX hwY

theorem C_pcc_congr_consT_arg1_code (B X Y : Term)
    (hB : ∀ W, Prf (substtc zero W B =eq B)) (hX : ∀ W, Prf (substtc zero W X =eq X))
    (hwB : Prf (hasWit B) := by hw_auto) (hwX : Prf (hasWit X) := by hw_auto)
    (hwY : Prf (hasWit Y) := by hw_auto) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (consT X B) (consT Y B))) :=
  pcc_congr_hole_code (fun s => consT s B) X Y
    (fun W => prf_eq_trans (prf_substtc_consT zero W X B) (prf_congr_consT (hX W) (hB W)))
    (fun w => prf_eq_trans (prf_substtc_consT zero w (varc (numeral 0)) B)
      (prf_congr_consT (prf_substtc_varc0 w) (hB w)))
    (prf_hasWit_consT hwX hwB) (prf_hasWit_consT (prf_hasWit_varc (numeral 0)) hwB) hwX hwY

/-! ### `Meta/LineWFTrackedPrf.lean` (1; el contexto DIAGONAL: el hueco aparece dos veces) -/

theorem C_pcc_congr_eqcT_diag_code_imp (X Y : Term)
    (hX : ∀ W, Prf (substtc zero W X =eq X))
    (hwX : Prf (hasWit X)) (hwY : Prf (hasWit Y)) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (eqcT X X) (eqcT Y Y))) :=
  pcc_congr_hole_code (fun s => eqcT s s) X Y
    (fun W => prf_eq_trans (prf_substtc_eqcT W X X) (prf_congr_eqcT (hX W) (hX W)))
    (fun w => prf_eq_trans (prf_substtc_eqcT w (varc (numeral 0)) (varc (numeral 0)))
      (prf_congr_eqcT (prf_substtc_varc0 w) (prf_substtc_varc0 w)))
    (prf_hasWit_eqcT hwX hwX)
    (prf_hasWit_eqcT (prf_hasWit_varc (numeral 0)) (prf_hasWit_varc (numeral 0))) hwX hwY

/-! ### `Meta/SubstfcCodePrf.lean` (1; la «octava» de 2026‑09) -/

theorem C_pcc_congr_substfcT_arg3_code (A B X Y : Term)
    (hA : ∀ W, Prf (substtc zero W A =eq A)) (hB : ∀ W, Prf (substtc zero W B =eq B))
    (hX : ∀ W, Prf (substtc zero W X =eq X))
    (hwA : Prf (hasWit A) := by hw_auto) (hwB : Prf (hasWit B) := by hw_auto)
    (hwX : Prf (hasWit X) := by hw_auto) (hwY : Prf (hasWit Y) := by hw_auto) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (substfcT A B X) (substfcT A B Y))) :=
  pcc_congr_hole_code (fun s => substfcT A B s) X Y
    (fun W => prf_eq_trans (prf_substtc_substfcT zero W A B X)
      (prf_congr_substfcT (hA W) (hB W) (hX W)))
    (fun w => prf_eq_trans (prf_substtc_substfcT zero w A B (varc (numeral 0)))
      (prf_congr_substfcT (hA w) (hB w) (prf_substtc_varc0 w)))
    (prf_hasWit_funcc3 (strCode sym!"substfc") A B X hwA hwB hwX)
    (prf_hasWit_funcc3 (strCode sym!"substfc") A B (varc (numeral 0)) hwA hwB
      (prf_hasWit_varc (numeral 0))) hwX hwY

/-! ### `Meta/TrackedAtomsPrf.lean` (1) -/

theorem C_pcc_congr_nthcT_arg1_code (B X Y : Term)
    (hB : ∀ W, Prf (substtc zero W B =eq B)) (hX : ∀ W, Prf (substtc zero W X =eq X))
    (hwB : Prf (hasWit B) := by hw_auto) (hwX : Prf (hasWit X) := by hw_auto)
    (hwY : Prf (hasWit Y) := by hw_auto) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (nthcT X B) (nthcT Y B))) :=
  pcc_congr_hole_code (fun s => nthcT s B) X Y
    (fun W => prf_eq_trans (prf_substtc_nthcT zero W X B) (prf_congr_nthcT (hX W) (hB W)))
    (fun w => prf_eq_trans (prf_substtc_nthcT zero w (varc (numeral 0)) B)
      (prf_congr_nthcT (prf_substtc_varc0 w) (hB w)))
    (prf_hasWit_funcc2 _ X B hwX hwB)
    (prf_hasWit_funcc2 _ (varc (numeral 0)) B (prf_hasWit_varc (numeral 0)) hwB) hwX hwY

/-! ### Las 19, MISMO TIPO que la del build (`Prf : Formula → Prop`: dos pruebas de la misma
     proposición son la misma constante salvo nombre; si la firma copiada difiriera, no tiparía). -/

example : @C_pcc_congr_binT_2_code = @ROBINSON_PlusPlus.Meta.CodeCtorKit.pcc_congr_binT_2_code := rfl
example : @C_pcc_congr_binT_1_code = @ROBINSON_PlusPlus.Meta.CodeCtorKit.pcc_congr_binT_1_code := rfl
example : @C_pcc_congr_unT_code = @ROBINSON_PlusPlus.Meta.CodeCtorKit.pcc_congr_unT_code := rfl
example : @C_pcc_congr_succ_code = @ROBINSON_PlusPlus.Meta.EvalArithPrf.pcc_congr_succ_code := rfl
example : @C_pcc_congr_succ_code_imp
    = @ROBINSON_PlusPlus.Meta.EvalArithPrf.pcc_congr_succ_code_imp := rfl
example : @C_pcc_congr_carcT_code_imp
    = @ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf.pcc_congr_carcT_code_imp := rfl
example : @C_pcc_congr_liftfcT_arg2_code
    = @ROBINSON_PlusPlus.Meta.EvalLiftfcPrf.pcc_congr_liftfcT_arg2_code := rfl
example : @C_pcc_congr_addcT1_code_imp
    = @ROBINSON_PlusPlus.Meta.EvalMulPrf.pcc_congr_addcT1_code_imp := rfl
example : @C_pcc_congr_predcT_code = @ROBINSON_PlusPlus.Meta.EvalPredPrf.pcc_congr_predcT_code := rfl
example : @C_pcc_congr_substfcT_arg2_code
    = @ROBINSON_PlusPlus.Meta.EvalSubstfcPrf.pcc_congr_substfcT_arg2_code := rfl
example : @C_pcc_congr_substtcT_arg3_code
    = @ROBINSON_PlusPlus.Meta.EvalSubsttcPrf.pcc_congr_substtcT_arg3_code := rfl
example : @C_pcc_congr_substtscT_arg3_code
    = @ROBINSON_PlusPlus.Meta.EvalSubsttcPrf.pcc_congr_substtscT_arg3_code := rfl
example : @C_pcc_congr_liftcT_arg2_code
    = @ROBINSON_PlusPlus.Meta.LiftcCodePrf.pcc_congr_liftcT_arg2_code := rfl
example : @C_pcc_congr_liftscT_arg2_code
    = @ROBINSON_PlusPlus.Meta.LiftcCodePrf.pcc_congr_liftscT_arg2_code := rfl
example : @C_pcc_congr_consT_arg2_code
    = @ROBINSON_PlusPlus.Meta.LiftcCodePrf.pcc_congr_consT_arg2_code := rfl
example : @C_pcc_congr_consT_arg1_code
    = @ROBINSON_PlusPlus.Meta.LiftcCodePrf.pcc_congr_consT_arg1_code := rfl
example : @C_pcc_congr_eqcT_diag_code_imp
    = @ROBINSON_PlusPlus.Meta.LineWFTrackedPrf.pcc_congr_eqcT_diag_code_imp := rfl
example : @C_pcc_congr_substfcT_arg3_code
    = @ROBINSON_PlusPlus.Meta.SubstfcCodePrf.pcc_congr_substfcT_arg3_code := rfl
example : @C_pcc_congr_nthcT_arg1_code
    = @ROBINSON_PlusPlus.Meta.TrackedAtomsPrf.pcc_congr_nthcT_arg1_code := rfl

/-! ## §3 · CONTROLES NEGATIVOS -/

/-- La técnica del `rfl` DISCRIMINA: dos copias de contexto distinto no tienen el mismo tipo. -/
example : True := by
  fail_if_success exact (rfl : @C_pcc_congr_binT_2_code
    = @ROBINSON_PlusPlus.Meta.CodeCtorKit.pcc_congr_binT_1_code)
  fail_if_success exact (rfl : @C_pcc_congr_consT_arg2_code
    = @ROBINSON_PlusPlus.Meta.LiftcCodePrf.pcc_congr_consT_arg1_code)
  fail_if_success exact (rfl : @C_pcc_congr_succ_code
    = @ROBINSON_PlusPlus.Meta.EvalArithPrf.pcc_congr_succ_code_imp)
  trivial

/-! ⚠️ Visto fallar (T48, 2026‑11‑02): con una hipótesis de más en la firma de
    `C_pcc_congr_unT_code` —sigue siendo demostrable— su `rfl` contra el build da «Type mismatch»;
    y el primer control de arriba, sin su `fail_if_success`, también. -/

end CongruenciaHueco

#print axioms CongruenciaHueco.pcc_congr_hole_code
#print axioms CongruenciaHueco.C_pcc_congr_binT_2_code
#print axioms CongruenciaHueco.C_pcc_congr_succ_code
#print axioms CongruenciaHueco.C_pcc_congr_eqcT_diag_code_imp
#print axioms CongruenciaHueco.C_pcc_congr_nthcT_arg1_code

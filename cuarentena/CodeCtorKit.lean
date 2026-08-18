/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.LineWFSchemaPrf

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.Representability
open ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.CheckArith
open ROBINSON_PlusPlus.Meta.Sigma1Prf
open ROBINSON_PlusPlus.Meta.TcArithPrf
open ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
open ROBINSON_PlusPlus.Meta.MpCodePrf
open ROBINSON_PlusPlus.Meta.EvalLtPrf
open ROBINSON_PlusPlus.Meta.EvalNthcPrf
open ROBINSON_PlusPlus.Meta.EvalListPrf
open ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf
open ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.LineWFTrackedPrf
open ROBINSON_PlusPlus.Meta.LineWFSchemaPrf

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Meta.CodeCtorKit

/-!
## META — NIVEL D real (B.3c): KIT de constructores de código, genérico en el TAG

Los constructores de código del lenguaje son **todos el mismo `cons`‑árbol** variando sólo su tag
numérico y su aridad:

  `botc` = ⟨2⟩ · `atomc` = ⟨3,·,·⟩ · `eqc` = ⟨4,·,·⟩ · `implc` = ⟨5,·,·⟩ · `forallc` = ⟨6,·⟩
  `andc` = ⟨7,·,·⟩ · `orc` = ⟨8,·,·⟩ · `exc` = ⟨9,·⟩

En vez de dar constructor object, congruencia, distribución de `substtc` y ecuación `tc` **para cada
uno** —que es lo que se hizo a mano con `eqcT` en `LineWFTrackedPrf`— se parametrizan por aridad y
tag: `nulT` / `unT` / `binT`. Con eso, `eqcT = binT 4` pasa a ser un caso particular, y los árboles
`E` de los 18 tags pendientes quedan cubiertos de un golpe.

La pieza que de verdad importa es la última sección: la **congruencia dentro de `Prov`**
(`pcc_congr_binT_{1,2}_code`, `pcc_congr_unT_code`), que generaliza el
`pcc_congr_eqcT_diag_code_imp` que `eqrefl` tuvo que construir a mano.
-/

/-- Constructor object de un código NULARIO de tag `m` (p. ej. `botc` = tag 2). -/
def nulT (m : Nat) : Term := consT (termCode (numeralM m)) (termCode nil)

/-- Constructor object de un código UNARIO de tag `m` (p. ej. `forallc` = 6, `exc` = 9). -/
def unT (m : Nat) (a : Term) : Term := consT (termCode (numeralM m)) (consT a (termCode nil))

/-- Constructor object de un código BINARIO de tag `m` (`eqc` = 4, `implc` = 5, `andc` = 7,
    `orc` = 8). -/
def binT (m : Nat) (a b : Term) : Term :=
  consT (termCode (numeralM m)) (consT a (consT b (termCode nil)))

/-- Puente definicional con `termCode`, caso nulario. -/
theorem nulT_termCode (m : Nat) : nulT m = termCode (cons (numeralM m) nil) := rfl

/-- Puente definicional con `termCode`, caso unario. -/
theorem unT_termCode (m : Nat) (a : Term) :
    unT m (termCode a) = termCode (cons (numeralM m) (cons a nil)) := rfl

/-- Puente definicional con `termCode`, caso binario. -/
theorem binT_termCode (m : Nat) (a b : Term) :
    binT m (termCode a) (termCode b) = termCode (cons (numeralM m) (cons a (cons b nil))) := rfl

/-! ### Congruencia y distribución de `substtc` -/

/-- Congruencia de `unT`. -/
theorem prf_congr_unT {m : Nat} {a a' : Term} (ha : Prf (a =eq a')) :
    Prf (unT m a =eq unT m a') := by
  unfold unT; exact prf_congr_consT (prf_refl _) (prf_congr_consT ha (prf_refl _))

/-- Congruencia de `binT` en ambos argumentos. -/
theorem prf_congr_binT {m : Nat} {a a' b b' : Term}
    (ha : Prf (a =eq a')) (hb : Prf (b =eq b')) : Prf (binT m a b =eq binT m a' b') := by
  unfold binT
  exact prf_congr_consT (prf_refl _) (prf_congr_consT ha (prf_congr_consT hb (prf_refl _)))

/-- `substtc` es la identidad sobre un código nulario (es cerrado). -/
theorem prf_substtc_nulT (m : Nat) (W : Term) :
    Prf (substtc zero W (nulT m) =eq nulT m) := by
  unfold nulT
  refine prf_eq_trans (prf_substtc_consT zero W _ _) ?_
  exact prf_congr_consT (substtc_inv_termCode_numeralM m W)
    (LineWFTrackedPrf.substtc_inv_termCode_of_tc prf_tc_zero W)

/-- `substtc` distribuye sobre `unT` (el tag y el `⌜nil⌝` son cerrados). -/
theorem prf_substtc_unT (m : Nat) (W a : Term) :
    Prf (substtc zero W (unT m a) =eq unT m (substtc zero W a)) := by
  unfold unT
  refine prf_eq_trans (prf_substtc_consT zero W _ _) ?_
  refine prf_congr_consT (substtc_inv_termCode_numeralM m W) ?_
  refine prf_eq_trans (prf_substtc_consT zero W _ _) ?_
  exact prf_congr_consT (prf_refl _)
    (LineWFTrackedPrf.substtc_inv_termCode_of_tc prf_tc_zero W)

/-- `substtc` distribuye sobre `binT`. -/
theorem prf_substtc_binT (m : Nat) (W a b : Term) :
    Prf (substtc zero W (binT m a b) =eq binT m (substtc zero W a) (substtc zero W b)) := by
  unfold binT
  refine prf_eq_trans (prf_substtc_consT zero W _ _) ?_
  refine prf_congr_consT (substtc_inv_termCode_numeralM m W) ?_
  refine prf_eq_trans (prf_substtc_consT zero W _ _) ?_
  refine prf_congr_consT (prf_refl _) ?_
  refine prf_eq_trans (prf_substtc_consT zero W _ _) ?_
  exact prf_congr_consT (prf_refl _)
    (LineWFTrackedPrf.substtc_inv_termCode_of_tc prf_tc_zero W)

/-- Invariancia `substtc` de `nulT` (forma `∀ W`, la que consumen los Leibniz internos). -/
theorem substtc_inv_nulT (m : Nat) : ∀ W, Prf (substtc zero W (nulT m) =eq nulT m) :=
  prf_substtc_nulT m

/-- Invariancia `substtc` de `unT`, heredada de la de su argumento. -/
theorem substtc_inv_unT {m : Nat} {a : Term}
    (ha : ∀ W, Prf (substtc zero W a =eq a)) :
    ∀ W, Prf (substtc zero W (unT m a) =eq unT m a) := fun W =>
  prf_eq_trans (prf_substtc_unT m W a) (prf_congr_unT (ha W))

/-- Invariancia `substtc` de `binT`, heredada de la de sus argumentos. -/
theorem substtc_inv_binT {m : Nat} {a b : Term}
    (ha : ∀ W, Prf (substtc zero W a =eq a)) (hb : ∀ W, Prf (substtc zero W b =eq b)) :
    ∀ W, Prf (substtc zero W (binT m a b) =eq binT m a b) := fun W =>
  prf_eq_trans (prf_substtc_binT m W a b) (prf_congr_binT (ha W) (hb W))

/-! ### Ecuaciones `tc` (el código del código, por aridad) -/

/-- `tcFn ⟨m⟩ = nulT m`. -/
theorem prf_tc_nul (m : Nat) : Prf (tcFn (cons (numeralM m) nil) =eq nulT m) := by
  unfold nulT
  exact prf_eq_trans (prf_tc_cons' _ _) (prf_congr_consT (prf_tc_numeralM m) prf_tc_zero)

/-- `tcFn ⟨m,a⟩ = unT m ȧ`. -/
theorem prf_tc_un (m : Nat) (a : Term) :
    Prf (tcFn (cons (numeralM m) (cons a nil)) =eq unT m (tcFn a)) := by
  unfold unT
  refine prf_eq_trans (prf_tc_cons' _ _) ?_
  refine prf_congr_consT (prf_tc_numeralM m) ?_
  exact prf_eq_trans (prf_tc_cons' _ _) (prf_congr_consT (prf_refl _) prf_tc_zero)

/-- `tcFn ⟨m,a,b⟩ = binT m ȧ ḃ`. -/
theorem prf_tc_bin (m : Nat) (a b : Term) :
    Prf (tcFn (cons (numeralM m) (cons a (cons b nil))) =eq binT m (tcFn a) (tcFn b)) := by
  unfold binT
  refine prf_eq_trans (prf_tc_cons' _ _) ?_
  refine prf_congr_consT (prf_tc_numeralM m) ?_
  refine prf_eq_trans (prf_tc_cons' _ _) ?_
  refine prf_congr_consT (prf_refl _) ?_
  exact prf_eq_trans (prf_tc_cons' _ _) (prf_congr_consT (prf_refl _) prf_tc_zero)

/-! ### Congruencia DENTRO de `Prov` (la pieza que cada reflector consume)

Cambiar un argumento del árbol de código **bajo `Prov`**, con la igualdad interna en la mano. Va
por Leibniz interno sobre un contexto de código de un solo hueco. Generaliza el
`pcc_congr_eqcT_diag_code_imp` que `eqrefl` construyó a mano (que era su caso diagonal). -/

/-- **Congruencia interna de `binT` en el 2º argumento**: de `Prov(⌜X = Y⌝)` sale
    `Prov(⌜binT m A X = binT m A Y⌝)`. -/
theorem pcc_congr_binT_2_code (m : Nat) (A X Y : Term)
    (hA : ∀ W, Prf (substtc zero W A =eq A)) (hX : ∀ W, Prf (substtc zero W X =eq X)) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (binT m A X) (binT m A Y))) := by
  let Ac : Term := eqc (binT m A X) (binT m A (varc (numeral 0)))
  have hcomp : ∀ w : Term, Prf (substfc zero w Ac =eq eqc (binT m A X) (binT m A w)) := by
    intro w
    refine prf_eq_trans (prf_substfc_eq zero w (binT m A X) (binT m A (varc (numeral 0)))) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · exact prf_eq_trans (prf_substtc_binT m w A X) (prf_congr_binT (hA w) (hX w))
    · exact prf_eq_trans (prf_substtc_binT m w A (varc (numeral 0)))
        (prf_congr_binT (hA w) (prf_substtc_varc0 w))
  have hAX : Prf (provFromCode (substfc zero X Ac)) :=
    prf_mp (prf_provCode_congr (prf_eq_symm (hcomp X)))
      (prf_provFromCode_eqCodeFn_refl (binT m A X))
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcomp Y)) _)
    (PrfH_leibniz_apply Ac X Y (prfH_hyp_self _) (prf_to_prfH hAX _))

/-- **Congruencia interna de `binT` en el 1er argumento**. -/
theorem pcc_congr_binT_1_code (m : Nat) (B X Y : Term)
    (hB : ∀ W, Prf (substtc zero W B =eq B)) (hX : ∀ W, Prf (substtc zero W X =eq X)) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (binT m X B) (binT m Y B))) := by
  let Ac : Term := eqc (binT m X B) (binT m (varc (numeral 0)) B)
  have hcomp : ∀ w : Term, Prf (substfc zero w Ac =eq eqc (binT m X B) (binT m w B)) := by
    intro w
    refine prf_eq_trans (prf_substfc_eq zero w (binT m X B) (binT m (varc (numeral 0)) B)) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · exact prf_eq_trans (prf_substtc_binT m w X B) (prf_congr_binT (hX w) (hB w))
    · exact prf_eq_trans (prf_substtc_binT m w (varc (numeral 0)) B)
        (prf_congr_binT (prf_substtc_varc0 w) (hB w))
  have hAX : Prf (provFromCode (substfc zero X Ac)) :=
    prf_mp (prf_provCode_congr (prf_eq_symm (hcomp X)))
      (prf_provFromCode_eqCodeFn_refl (binT m X B))
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcomp Y)) _)
    (PrfH_leibniz_apply Ac X Y (prfH_hyp_self _) (prf_to_prfH hAX _))

/-- **Congruencia interna de `unT`**. -/
theorem pcc_congr_unT_code (m : Nat) (X Y : Term)
    (hX : ∀ W, Prf (substtc zero W X =eq X)) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (unT m X) (unT m Y))) := by
  let Ac : Term := eqc (unT m X) (unT m (varc (numeral 0)))
  have hcomp : ∀ w : Term, Prf (substfc zero w Ac =eq eqc (unT m X) (unT m w)) := by
    intro w
    refine prf_eq_trans (prf_substfc_eq zero w (unT m X) (unT m (varc (numeral 0)))) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · exact prf_eq_trans (prf_substtc_unT m w X) (prf_congr_unT (hX w))
    · exact prf_eq_trans (prf_substtc_unT m w (varc (numeral 0)))
        (prf_congr_unT (prf_substtc_varc0 w))
  have hAX : Prf (provFromCode (substfc zero X Ac)) :=
    prf_mp (prf_provCode_congr (prf_eq_symm (hcomp X)))
      (prf_provFromCode_eqCodeFn_refl (unT m X))
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcomp Y)) _)
    (PrfH_leibniz_apply Ac X Y (prfH_hyp_self _) (prf_to_prfH hAX _))

end ROBINSON_PlusPlus.Meta.CodeCtorKit

export ROBINSON_PlusPlus.Meta.CodeCtorKit (
  nulT unT binT nulT_termCode unT_termCode binT_termCode
  prf_congr_unT prf_congr_binT
  prf_substtc_nulT prf_substtc_unT prf_substtc_binT
  substtc_inv_nulT substtc_inv_unT substtc_inv_binT
  prf_tc_nul prf_tc_un prf_tc_bin
  pcc_congr_binT_1_code pcc_congr_binT_2_code pcc_congr_unT_code
)

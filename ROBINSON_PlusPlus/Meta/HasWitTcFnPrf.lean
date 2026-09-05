/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.CodeWitnessPrf
import ROBINSON_PlusPlus.Meta.NatArithPrf
import ROBINSON_PlusPlus.Meta.Sigma1Prf
import ROBINSON_PlusPlus.Meta.NumListPrf

/-!
# `∀t. hasWit (tcFn t)` — la buena formación de los códigos PUNTEADOS

Promovido de `sondeos/HasWitTcFn.lean` (2026-09-05). Es el prerrequisito que §3.32.2 identificó
para la vía C ([ADR-020](../../DECISIONS.md)) y que la propagación demostró **portante en dos
sitios**, no en uno:

1. el reflector Σ₁ del conjunto extra (`hasWitF` sobre código abstracto), y
2. el **sistema de prueba interno a nivel de código** — `pcc_exIntro_code'` y
   `pcc_forallElim_code` construyen líneas Q1/Q2 cuya carga es `tcFn a` con `a` ABSTRACTO, y bajo
   la enmienda esas líneas ya no son válidas sin la guarda.

## Por qué la ruta es única, y quedó medido antes de empezar

`tcFn` es un ATOMO OPACO (`Term.func "tcFn" [t]`) caracterizado por **sólo dos axiomas vivos**:
`ax_tc_zero` y `ax_tc_succ` (`ax_tc_cons` sigue RETIRADO por la reparación de inconsistencia).
Para `t` abstracto no hay nada que desplegar ⟹ la única ruta es **inducción OBJETO** sobre
`zero`/`succ`, que es exactamente el fragmento que esos dos axiomas cubren.

## Lo que aporta, y es genérico

Las tres piezas de §3 y §4 (`prf_argsIn_mono`, `prf_isTermCodeE1_mono`, `prf_wfAll1_cons`) **no
son específicas de `tcFn`**: valen para cualquier extensión de testigo, así que sirven igual al
lado `hasWitF`. No existían: cero apariciones de `argsIn_mono` / `wfAll1_mono` en producción y en
los 57 sondeos.

⚠️ **LA MONEDA DE LA INDUCCION OBJETO** (§3.31): el paso NO puede llevar la HI como hipótesis
META. Tiene que ser la implicación OBJETO `∀. Φ ⇒ Φ[σ#0]`, que es la firma de `prf_nat_induction`.

**Footprint**: `[propext, Classical.choice, Quot.sound]` — **net-0 puro**, ni un axioma del
proyecto (la inducción entra por `Prf.ind`, constructor del cálculo).
-/

open FOL
open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.NatArithPrf
open ROBINSON_PlusPlus.Meta.BoundedInPrf
open ROBINSON_PlusPlus.Meta.Sigma1Prf
open ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.NumListPrf
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf.ENS

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Meta.HasWitTcFnPrf

/-! ## §1 · El encuadre -/

/-- La fórmula sobre la que se induce: «el código punteado de `#0` tiene testigo». -/
def PHI : Formula := hasWit (tcFn (.var 0))

/-- `PHI` instanciada es lo que se espera. -/
theorem PHI_at (t : Term) : substFormula 0 t PHI = hasWit (tcFn t) := by
  simp only [PHI, substF_hasWit, tcFn, substTerm, substTerms, if_true]

/-! ## §2 · LA BASE — y sale GRATIS de la rama A

`termCodeM zero` es **literalmente** el RHS de `ax_tc_zero`:
`termCodeM (.func zero_sym []) = ⟨1̄, strCodeM zero_sym, termsCodeM []⟩ = ⟨1̄, strCodeM 0, nil⟩`.
Luego la base es `CRIT_hasWit_real zero` transportada por el axioma. -/

/-- El axioma `ax_tc_zero` en `Prf`. -/
theorem termCodeM_zero_eq :
    termCodeM zero = cons (numeralM 1) (cons (strCodeM zero_sym) (cons nil nil)) := rfl

theorem prf_ax_tc_zero : Prf (tcFn zero =eq termCodeM zero) := by
  have h := prf_ax (show ax_tc_zero ∈ axioms by simp [axioms])
  rw [termCodeM_zero_eq]
  simpa only [ax_tc_zero] using h

/-- **BASE**: `hasWit (tcFn 0)`. -/
theorem base : Prf (substFormula 0 zero PHI) := by
  rw [PHI_at]
  exact prf_congr_hasWit (prf_eq_symm prf_ax_tc_zero) (CRIT_hasWit_real zero)

/-! ## §3 · MONOTONIA DEL TESTIGO — la pieza que NO existía

El paso inductivo extiende el testigo (`w ↦ cons A w`), y para que los elementos VIEJOS sigan
siendo nodos bien formados hace falta que `argsIn` sea monótona en su testigo. No estaba: cero
apariciones de `argsIn_mono` / `wfAll1_mono` en producción y en los 57 sondeos.

Patrón calcado de `prf_argsIn_tail` (`Meta/CodeWitnessPrf.lean`): `Prf.qconf` + `Prf.gen` para
entrar bajo el `∀` acotado, `PrfH_inst_argsIn` para instanciar la hipótesis. -/

/-- **`argsIn` es MONOTONA en el testigo.** -/
theorem prf_argsIn_mono (a w Y : Term) :
    Prf (Formula.impl (argsIn w Y) (argsIn (cons a w) Y)) := by
  refine prf_mp (Prf.qconf (argsIn w Y) (argsInBody (cons a w) Y)) (Prf.gen _ ?_)
  rw [liftF_argsIn]
  refine prf_deduction (deduction_aux ?_ (lt (.var 0) (liftTerm 0 (lenc Y)))
    [argsIn (liftTerm 0 w) (liftTerm 0 Y)] rfl)
  show PrfH [lt (.var 0) (lenc (liftTerm 0 Y)), argsIn (liftTerm 0 w) (liftTerm 0 Y)]
    (In (nthc (liftTerm 0 Y) (.var 0)) (cons (liftTerm 0 a) (liftTerm 0 w)))
  have hlt : PrfH [lt (.var 0) (lenc (liftTerm 0 Y)), argsIn (liftTerm 0 w) (liftTerm 0 Y)]
      (lt (.var 0) (lenc (liftTerm 0 Y))) := PrfH.hyp _ _ (List.Mem.head _)
  have hargs : PrfH [lt (.var 0) (lenc (liftTerm 0 Y)), argsIn (liftTerm 0 w) (liftTerm 0 Y)]
      (argsIn (liftTerm 0 w) (liftTerm 0 Y)) := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hin := PrfH.mp _ _ _
    (PrfH_inst_argsIn (liftTerm 0 w) (liftTerm 0 Y) (.var 0) hargs) hlt
  exact PrfH.mp _ _ _
    (prf_to_prfH (prf_in_cons_tail_imp (liftTerm 0 a)
      (nthc (liftTerm 0 Y) (.var 0)) (liftTerm 0 w)) _) hin

/-- **`isTermCodeE1` es MONOTONO en el testigo** (el testigo sólo aparece en `argsIn`). -/
theorem prf_isTermCodeE1_mono (a w X : Term) :
    Prf (Formula.impl (isTermCodeE1 w X) (isTermCodeE1 (cons a w) X)) := by
  unfold isTermCodeE1
  refine prf_or_elim_imp ?_ ?_
  · exact Prf.incl (Prf₀.j1 _ _)
  · refine prf_deduction ?_
    have hh : PrfH [land (shapeBin X 1) (argsIn w (nthc X (numeralM 2)))]
        (land (shapeBin X 1) (argsIn w (nthc X (numeralM 2)))) := prfH_hyp_self _
    have h1 := PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.c2 _ _)) hh
    have h2 := PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.c3 _ _)) hh
    have h2' := PrfH.mp _ _ _
      (prf_to_prfH (prf_argsIn_mono a w (nthc X (numeralM 2))) _) h2
    exact PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.j2 _ _))
      (PrfH.mp _ _ _ (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.c1 _ _)) h1) h2')

/-! ## §4 · `wfAll1` DE UN TESTIGO EXTENDIDO — el corazón del paso

`wfAll1 (cons A w)` pide que TODA posición sea nodo bien formado. La 0 es `A` (hipótesis);
las demás son las de `w`, que lo eran contra `w` y lo siguen siendo contra `cons A w` por §3.
El corte por casos del índice va con `prf_zero_or_eq_succ_pred` (`Meta/BoundedInPrf.lean`),
que es la reformulación SIN `∃` — justo para poder partir dentro de un `PrfH`. -/

/-- Contexto base del `∀` acotado (índice + conjunción de hipótesis). -/
def CTX0 (A w : Term) : List Formula :=
  [lt (.var 0) (lenc (cons (liftTerm 0 A) (liftTerm 0 w))),
   land (isTermCodeE1 (cons (liftTerm 0 A) (liftTerm 0 w)) (liftTerm 0 A))
     (wfAll1 (liftTerm 0 w))]

theorem prf_wfAll1_cons (A w : Term) :
    Prf (Formula.impl (land (isTermCodeE1 (cons A w) A) (wfAll1 w)) (wfAll1 (cons A w))) := by
  refine prf_mp (Prf.qconf (land (isTermCodeE1 (cons A w) A) (wfAll1 w))
    (wfAll1Body (cons A w))) (Prf.gen _ ?_)
  simp only [liftFormula, liftF_isTermCodeE1, liftF_wfAll1, land]
  refine prf_deduction (deduction_aux ?_
    (lt (.var 0) (liftTerm 0 (lenc (cons A w))))
    [land (isTermCodeE1 (cons (liftTerm 0 A) (liftTerm 0 w)) (liftTerm 0 A))
      (wfAll1 (liftTerm 0 w))] rfl)
  have hlt : PrfH [lt (.var 0) (lenc (cons (liftTerm 0 A) (liftTerm 0 w))),
      land (isTermCodeE1 (cons (liftTerm 0 A) (liftTerm 0 w)) (liftTerm 0 A))
        (wfAll1 (liftTerm 0 w))]
      (lt (.var 0) (lenc (cons (liftTerm 0 A) (liftTerm 0 w)))) :=
    PrfH.hyp _ _ (List.Mem.head _)
  have hand : PrfH [lt (.var 0) (lenc (cons (liftTerm 0 A) (liftTerm 0 w))),
      land (isTermCodeE1 (cons (liftTerm 0 A) (liftTerm 0 w)) (liftTerm 0 A))
        (wfAll1 (liftTerm 0 w))]
      (land (isTermCodeE1 (cons (liftTerm 0 A) (liftTerm 0 w)) (liftTerm 0 A))
        (wfAll1 (liftTerm 0 w))) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hA := PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.c2 _ _)) hand
  have hw := PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.c3 _ _)) hand
  clear hA hw
  refine PrfH_or_elim (prf_to_prfH (prf_zero_or_eq_succ_pred (.var 0)) _) ?zc ?sc
  case zc =>
    have hz : PrfH (Formula.eq (.var 0) zero :: CTX0 A w) (Formula.eq (.var 0) zero) := PrfH.hyp _ _ (List.Mem.head _)
    have hand2 : PrfH (Formula.eq (.var 0) zero :: CTX0 A w)
        (land (isTermCodeE1 (cons (liftTerm 0 A) (liftTerm 0 w)) (liftTerm 0 A))
          (wfAll1 (liftTerm 0 w))) :=
      PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    have hA2 := PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.c2 _ _)) hand2
    have hnth : PrfH (Formula.eq (.var 0) zero :: CTX0 A w) (nthc (cons (liftTerm 0 A) (liftTerm 0 w)) (.var 0) =eq liftTerm 0 A) :=
      PrfH_eq_trans (PrfH_congr_nthc_idx _ hz)
        (prf_to_prfH (prf_nthc_zero (liftTerm 0 A) (liftTerm 0 w)) _)
    exact PrfH_congr_isTermCodeE1 (PrfH_eq_symm hnth) hA2
  case sc =>
    have hs : PrfH (Formula.eq (.var 0) (succ (pred (.var 0))) :: CTX0 A w) (Formula.eq (.var 0) (succ (pred (.var 0)))) := PrfH.hyp _ _ (List.Mem.head _)
    have hlt2 : PrfH (Formula.eq (.var 0) (succ (pred (.var 0))) :: CTX0 A w) (lt (.var 0) (lenc (cons (liftTerm 0 A) (liftTerm 0 w)))) :=
      PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
    have hand2 : PrfH (Formula.eq (.var 0) (succ (pred (.var 0))) :: CTX0 A w)
        (land (isTermCodeE1 (cons (liftTerm 0 A) (liftTerm 0 w)) (liftTerm 0 A))
          (wfAll1 (liftTerm 0 w))) :=
      PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    have hw2 := PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.c3 _ _)) hand2
    have hltS : PrfH (Formula.eq (.var 0) (succ (pred (.var 0))) :: CTX0 A w) (lt (succ (pred (.var 0))) (succ (lenc (liftTerm 0 w)))) :=
      ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2 (prf_to_prfH (prf_lenc_cons (liftTerm 0 A) (liftTerm 0 w)) _)
        (ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst1 hs hlt2)
    have hltw : PrfH (Formula.eq (.var 0) (succ (pred (.var 0))) :: CTX0 A w) (lt (pred (.var 0)) (lenc (liftTerm 0 w))) :=
      PrfH.mp _ _ _ (prf_to_prfH
        (prf_lt_of_succ_lt_succ (pred (.var 0)) (lenc (liftTerm 0 w))) _) hltS
    have hnode : PrfH (Formula.eq (.var 0) (succ (pred (.var 0))) :: CTX0 A w) (isTermCodeE1 (liftTerm 0 w) (nthc (liftTerm 0 w) (pred (.var 0)))) :=
      PrfH.mp _ _ _ (PrfH_inst_wfAll1 (liftTerm 0 w) (pred (.var 0)) hw2) hltw
    have hmono : PrfH (Formula.eq (.var 0) (succ (pred (.var 0))) :: CTX0 A w) (isTermCodeE1 (cons (liftTerm 0 A) (liftTerm 0 w))
        (nthc (liftTerm 0 w) (pred (.var 0)))) :=
      PrfH.mp _ _ _ (prf_to_prfH (prf_isTermCodeE1_mono (liftTerm 0 A) (liftTerm 0 w)
        (nthc (liftTerm 0 w) (pred (.var 0)))) _) hnode
    have hnth : PrfH (Formula.eq (.var 0) (succ (pred (.var 0))) :: CTX0 A w) (nthc (cons (liftTerm 0 A) (liftTerm 0 w)) (.var 0)
        =eq nthc (liftTerm 0 w) (pred (.var 0))) :=
      PrfH_eq_trans (PrfH_congr_nthc_idx _ hs)
        (prf_to_prfH (prf_nthc_succ (liftTerm 0 A) (liftTerm 0 w) (pred (.var 0))) _)
    exact PrfH_congr_isTermCodeE1 (PrfH_eq_symm hnth) hmono

/-! ## §5 · EL NODO `σ`

`ax_tc_succ` dice que `tcFn (σ x)` es el nodo funcional `⟨1̄, ⌜σ⌝, [tcFn x]⟩`. Espejo en `Prf`
de `Meta/Diagonal.tc_succ` (que está en `⊢`), y en vocabulario `Minimal` (`numeralM`/`strCodeM`),
que es el que usan las guardas. -/

/-- El nodo que `ax_tc_succ` asigna a `tcFn (σ x)`. -/
def SUCCNODE (x : Term) : Term :=
  cons (numeralM 1) (cons (strCodeM succ_sym) (cons (cons (tcFn x) nil) nil))

theorem prf_ax_tc_succ (x : Term) : Prf (tcFn (succ x) =eq SUCCNODE x) := by
  have h := prf_spec (prf_ax (show ax_tc_succ ∈ axioms by simp [axioms])) x
  simpa only [ax_tc_succ, SUCCNODE, substFormula, substTerm, substTerms, tcFn, succ, cons, nil,
    zero, substTerm_numeralM, substTerm_strCodeM, substTerm_nil,
    FOL.substTerm_liftTerm, if_true] using h

/-! ## §6 · `argsIn` DE UN SINGLETON

La lista de argumentos del nodo `σ` tiene UN elemento. `argsIn W [hd]` se reduce a `In hd W`:
la posición 0 es `hd`, y no hay más porque `lenc nil = 0` cierra el caso sucesor por `efq`. -/

theorem prf_argsIn_singleton (W hd : Term) :
    Prf (Formula.impl (In hd W) (argsIn W (cons hd nil))) := by
  refine prf_mp (Prf.qconf (In hd W) (argsInBody W (cons hd nil))) (Prf.gen _ ?_)
  simp only [liftFormula, In, liftTerm, liftTerms]
  refine prf_deduction (deduction_aux ?_
    (lt (.var 0) (liftTerm 0 (lenc (cons hd nil))))
    [In (liftTerm 0 hd) (liftTerm 0 W)] rfl)
  refine PrfH_or_elim (prf_to_prfH (prf_zero_or_eq_succ_pred (.var 0)) _) ?zc ?sc
  case zc =>
    have hz : PrfH (Formula.eq (.var 0) zero ::
        [lt (.var 0) (lenc (cons (liftTerm 0 hd) nil)), In (liftTerm 0 hd) (liftTerm 0 W)])
        (Formula.eq (.var 0) zero) := PrfH.hyp _ _ (List.Mem.head _)
    have hin : PrfH (Formula.eq (.var 0) zero ::
        [lt (.var 0) (lenc (cons (liftTerm 0 hd) nil)), In (liftTerm 0 hd) (liftTerm 0 W)])
        (In (liftTerm 0 hd) (liftTerm 0 W)) :=
      PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    have hnth : PrfH (Formula.eq (.var 0) zero ::
        [lt (.var 0) (lenc (cons (liftTerm 0 hd) nil)), In (liftTerm 0 hd) (liftTerm 0 W)])
        (nthc (cons (liftTerm 0 hd) nil) (.var 0) =eq liftTerm 0 hd) :=
      PrfH_eq_trans (PrfH_congr_nthc_idx _ hz)
        (prf_to_prfH (prf_nthc_zero (liftTerm 0 hd) nil) _)
    exact PrfH_congr_In_left (PrfH_eq_symm hnth) hin
  case sc =>
    have hs : PrfH (Formula.eq (.var 0) (succ (pred (.var 0))) ::
        [lt (.var 0) (lenc (cons (liftTerm 0 hd) nil)), In (liftTerm 0 hd) (liftTerm 0 W)])
        (Formula.eq (.var 0) (succ (pred (.var 0)))) := PrfH.hyp _ _ (List.Mem.head _)
    have hlt2 : PrfH (Formula.eq (.var 0) (succ (pred (.var 0))) ::
        [lt (.var 0) (lenc (cons (liftTerm 0 hd) nil)), In (liftTerm 0 hd) (liftTerm 0 W)])
        (lt (.var 0) (lenc (cons (liftTerm 0 hd) nil))) :=
      PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
    have hltS : PrfH (Formula.eq (.var 0) (succ (pred (.var 0))) ::
        [lt (.var 0) (lenc (cons (liftTerm 0 hd) nil)), In (liftTerm 0 hd) (liftTerm 0 W)])
        (lt (succ (pred (.var 0))) (succ (lenc nil))) :=
      ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2
        (prf_to_prfH (prf_lenc_cons (liftTerm 0 hd) nil) _)
        (ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst1 hs hlt2)
    have hzero : PrfH (Formula.eq (.var 0) (succ (pred (.var 0))) ::
        [lt (.var 0) (lenc (cons (liftTerm 0 hd) nil)), In (liftTerm 0 hd) (liftTerm 0 W)])
        (lt (pred (.var 0)) zero) :=
      ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2 (prf_to_prfH prf_lenc_nil _)
        (PrfH.mp _ _ _ (prf_to_prfH
          (prf_lt_of_succ_lt_succ (pred (.var 0)) (lenc nil)) _) hltS)
    exact PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.efq _))
      (PrfH.mp _ _ _ (prf_to_prfH (prf_not_lt_zero (pred (.var 0))) _) hzero)

/-! ## §7 · EL NODO `σ` ES UN `isTermCodeE1` — si su argumento está en el testigo -/

theorem prf_nthc_succnode_1 (x : Term) :
    Prf (nthc (SUCCNODE x) (numeralM 1) =eq strCodeM succ_sym) :=
  prf_eq_trans (prf_nthc_succ _ _ _) (prf_nthc_zero _ _)

theorem prf_nthc_succnode_2 (x : Term) :
    Prf (nthc (SUCCNODE x) (numeralM 2) =eq cons (tcFn x) nil) :=
  prf_eq_trans (prf_nthc_succ _ _ _)
    (prf_eq_trans (prf_nthc_succ _ _ _) (prf_nthc_zero _ _))

/-- El nodo `σ` tiene la FORMA BINARIA del tag 1 (`funcc`). -/
theorem prf_shapeBin_succnode (x : Term) : Prf (shapeBin (SUCCNODE x) 1) := by
  refine prf_eq_symm (prf_congr_cons_tail ?_)
  exact prf_eq_trans (prf_congr_cons_head (prf_nthc_succnode_1 x))
    (prf_congr_cons_tail (prf_congr_cons_head (prf_nthc_succnode_2 x)))

/-- **El nodo `σ` es nodo bien formado** contra cualquier testigo que contenga `tcFn x`. -/
theorem prf_isTermCodeE1_succnode (W x : Term) :
    Prf (Formula.impl (In (tcFn x) W) (isTermCodeE1 W (SUCCNODE x))) := by
  unfold isTermCodeE1
  refine prf_deduction ?_
  have hin : PrfH [In (tcFn x) W] (In (tcFn x) W) := prfH_hyp_self _
  have hargs : PrfH [In (tcFn x) W] (argsIn W (cons (tcFn x) nil)) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_argsIn_singleton W (tcFn x)) _) hin
  have hargs2 : PrfH [In (tcFn x) W] (argsIn W (nthc (SUCCNODE x) (numeralM 2))) :=
    PrfH_congr_argsIn (PrfH_eq_symm (prf_to_prfH (prf_nthc_succnode_2 x) _)) hargs
  exact PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.j2 _ _))
    (PrfH.mp _ _ _ (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.c1 _ _))
      (prf_to_prfH (prf_shapeBin_succnode x) _)) hargs2)

/-! ## §8 · Congruencia de `hasWit` en `PrfH` (la necesita el ensamblaje) -/

theorem PrfH_congr_hasWit {Γ : List Formula} {a b : Term}
    (h : PrfH Γ (a =eq b)) (hw : PrfH Γ (hasWit a)) : PrfH Γ (hasWit b) := by
  have e : ∀ s : Term, substFormula 0 s (hasWit (.var 0)) = hasWit s := by
    intro s; simp only [substF_hasWit, substTerm, if_true]
  exact (e b) ▸ ROBINSON_PlusPlus.Meta.ChainPrf.PrfH_leibniz_subst
    (A := hasWit (.var 0)) h ((e a) ▸ hw)

/-! ## §9 · EL PASO INDUCTIVO — ensamblaje `∃`-elim / `∃`-intro

Molde: `CRIT_hasWit_lift` (`Meta/CodeWitnessPrf.lean`), que hace la misma gimnasia de lifts.
Del testigo VIEJO (`#0`, el ligado por el `∃` de la hipótesis) se construye el NUEVO,
`cons (nodo σ) #0`, y §4 se encarga de que siga siendo un testigo bien formado. -/

theorem liftT_SUCCNODE (k : Nat) (x : Term) :
    liftTerm k (SUCCNODE x) = SUCCNODE (liftTerm k x) := by
  simp only [SUCCNODE, tcFn, cons, nil, zero, liftTerm, liftTerms, liftTerm_numeralM,
    liftTerm_strCodeM]

set_option maxRecDepth 8000 in
theorem step_at (x : Term) :
    Prf (Formula.impl (hasWit (tcFn x)) (hasWit (SUCCNODE x))) := by
  refine prf_ex_elim_imp ?_
  have hgoal : liftFormula 0 (hasWit (SUCCNODE x))
      = Formula.ex (isTC1 (.var 0) (liftTerm 1 (liftTerm 0 (SUCCNODE x)))) := by
    simp only [hasWit, liftFormula, liftF_isTC1, liftTerm, Nat.reduceAdd,
      Nat.zero_lt_succ, reduceIte]
  rw [hgoal]
  refine PrfH_ex_intro (cons (liftTerm 0 (SUCCNODE x)) (.var 0)) ?_
  have hsub : substFormula 0 (cons (liftTerm 0 (SUCCNODE x)) (.var 0))
      (isTC1 (.var 0) (liftTerm 1 (liftTerm 0 (SUCCNODE x))))
      = isTC1 (cons (liftTerm 0 (SUCCNODE x)) (.var 0)) (liftTerm 0 (SUCCNODE x)) := by
    rw [← FOL.liftTerm_comm_zero, substF_isTC1, FOL.substTerm_liftTerm]
    simp only [substTerm, if_true]
  rw [hsub]
  -- el contexto trae `isTC1 #0 ↑(tcFn x)`
  have hctx : PrfH [isTC1 (.var 0) (liftTerm 0 (tcFn x))]
      (isTC1 (.var 0) (liftTerm 0 (tcFn x))) := prfH_hyp_self _
  have hwf : PrfH [isTC1 (.var 0) (liftTerm 0 (tcFn x))] (wfAll1 (.var 0)) := by
    have := PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.c2 _ _)) hctx
    simpa only [isTC1, land] using this
  have hin0 : PrfH [isTC1 (.var 0) (liftTerm 0 (tcFn x))]
      (In (liftTerm 0 (tcFn x)) (.var 0)) := by
    have := PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.c3 _ _)) hctx
    simpa only [isTC1, land] using this
  -- el argumento del nodo sigue en el testigo EXTENDIDO
  have hinW : PrfH [isTC1 (.var 0) (liftTerm 0 (tcFn x))]
      (In (tcFn (liftTerm 0 x)) (cons (liftTerm 0 (SUCCNODE x)) (.var 0))) := by
    refine PrfH.mp _ _ _ (prf_to_prfH (prf_in_cons_tail_imp (liftTerm 0 (SUCCNODE x))
      (tcFn (liftTerm 0 x)) (.var 0)) _) ?_
    simpa only [tcFn, liftTerm, liftTerms] using hin0
  -- el nodo σ es nodo bien formado contra ese testigo
  have hnode : PrfH [isTC1 (.var 0) (liftTerm 0 (tcFn x))]
      (isTermCodeE1 (cons (liftTerm 0 (SUCCNODE x)) (.var 0)) (liftTerm 0 (SUCCNODE x))) := by
    rw [liftT_SUCCNODE]
    exact PrfH.mp _ _ _ (prf_to_prfH (prf_isTermCodeE1_succnode
      (cons (SUCCNODE (liftTerm 0 x)) (.var 0)) (liftTerm 0 x)) _) hinW
  -- §4 cierra `wfAll1` del testigo extendido
  have hwf' : PrfH [isTC1 (.var 0) (liftTerm 0 (tcFn x))]
      (wfAll1 (cons (liftTerm 0 (SUCCNODE x)) (.var 0))) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_wfAll1_cons (liftTerm 0 (SUCCNODE x)) (.var 0)) _)
      (PrfH.mp _ _ _ (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.c1 _ _)) hnode) hwf)
  have hinH : PrfH [isTC1 (.var 0) (liftTerm 0 (tcFn x))]
      (In (liftTerm 0 (SUCCNODE x)) (cons (liftTerm 0 (SUCCNODE x)) (.var 0))) :=
    prf_to_prfH (prf_in_cons_head _ _) _
  simpa only [isTC1, land] using
    PrfH.mp _ _ _ (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.c1 _ _)) hwf') hinH

/-! ## §10 · EL CIERRE — inducción objeto -/

/-- Silogismo hipotético en `Prf` (local: `prf_imp_trans` vive en `LineWFCases`, aguas abajo). -/
theorem prf_syll {a b c : Formula} (h1 : Prf (a ⇒ b)) (h2 : Prf (b ⇒ c)) : Prf (a ⇒ c) :=
  prf_mp (prf_mp (Prf.incl (Prf₀.p2 a b c))
    (prf_mp (Prf.incl (Prf₀.p1 (Formula.impl b c) a)) h2)) h1

/-- Congruencia de `hasWit` en forma de IMPLICACION. -/
theorem prf_congr_hasWit_imp {a b : Term} (h : Prf (a =eq b)) :
    Prf (Formula.impl (hasWit a) (hasWit b)) :=
  prf_deduction (PrfH_congr_hasWit (prf_to_prfH h _) (prfH_hyp_self _))

/-- El paso, ya en la forma `tcFn (σ x)`. -/
theorem step_full (x : Term) :
    Prf (Formula.impl (hasWit (tcFn x)) (hasWit (tcFn (succ x)))) :=
  prf_syll (step_at x) (prf_congr_hasWit_imp (prf_eq_symm (prf_ax_tc_succ x)))

/-- El paso en la forma EXACTA que pide `prf_nat_induction` (la moneda OBJETO). -/
theorem step : Prf (Formula.forall (Formula.impl PHI
    (substFormula 0 (succ (.var 0)) (liftFormula 1 PHI)))) := by
  have h : substFormula 0 (succ (.var 0)) (liftFormula 1 PHI)
      = hasWit (tcFn (succ (.var 0))) := by
    simp [PHI, liftF_hasWit, substF_hasWit, tcFn, liftTerm, liftTerms,
      substTerm, substTerms]
  rw [h]
  exact Prf.gen _ (step_full (.var 0))

/-- **`∀. hasWit (tcFn #0)`** — el enunciado OBJETO. -/
theorem prf_hasWit_tcFn_all : Prf (Formula.forall PHI) :=
  prf_nat_induction PHI base step

/-- 🏁 **EL LEMA: `∀t. hasWit (tcFn t)`.**

    El prerrequisito que §3.32.2 identificó para la vía C y que resultó PORTANTE EN DOS SITIOS:
    el reflector Σ₁ del conjunto extra, y el sistema de prueba interno a nivel de código
    (`pcc_exIntro_code'` / `pcc_forallElim_code`), que construye líneas Q1/Q2 con carga `tcFn a`
    para `a` ABSTRACTO. -/
theorem prf_hasWit_tcFn (t : Term) : Prf (hasWit (tcFn t)) := by
  have h := prf_spec prf_hasWit_tcFn_all t
  rwa [PHI_at] at h

end ROBINSON_PlusPlus.Meta.HasWitTcFnPrf

export ROBINSON_PlusPlus.Meta.HasWitTcFnPrf (
  prf_hasWit_tcFn prf_hasWit_tcFn_all
  prf_argsIn_mono prf_isTermCodeE1_mono prf_wfAll1_cons
  PrfH_congr_hasWit prf_congr_hasWit_imp
)


/-! ## §11 · FOOTPRINT -/
#print axioms ROBINSON_PlusPlus.Meta.HasWitTcFnPrf.prf_hasWit_tcFn
#print axioms ROBINSON_PlusPlus.Meta.HasWitTcFnPrf.prf_argsIn_mono
#print axioms ROBINSON_PlusPlus.Meta.HasWitTcFnPrf.prf_wfAll1_cons

/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.BoundedInPrf
import ROBINSON_PlusPlus.Meta.CantorMonoPrf
import ROBINSON_PlusPlus.Meta.HasWitTcFnPrf
import ROBINSON_PlusPlus.Meta.NumCodeClosedPrf
import ROBINSON_PlusPlus.Meta.StrongInductionPrf
import ROBINSON_PlusPlus.Meta.SubstArith

/-!
# La CLAUSURA de las guardas bajo la sustitución OBJETO — `substtc` y `substfc`

Promovido de `sondeos/ClausuraSubsttc.lean` (2026-09-06). Es **la pieza que cerraba la vía C**
([ADR-020](../../DECISIONS.md)): §3.36.5 la identificó como *lo único que separaba el árbol del
verde*, y §3.38 la documenta.

```
prf_hasWit_substtc  (v s t) : Prf (hasWit t  ⇒ (hasWit s ⇒ hasWit  (substtc v s t)))
prf_hasWitF_substfc (v s X) : Prf (hasWitF X ⇒ (hasWit s ⇒ hasWitF (substfc v s X)))
```

Las dos con el **código y el sustituyendo ABSTRACTOS**, que es la forma que consume la familia
`pcc_*_inst*` de `Meta/MpCodePrf.lean` bajo la enmienda.

## Son DOS clausuras, y la de FÓRMULA consume la de TÉRMINO

Los casos `atomc` y `eqc` del código de fórmula tienen argumentos de sorte TÉRMINO, así que piden
`hasWit (substtc v s t)`. Por eso la mitad término va primero — y por eso la mitad fórmula
**no es conjuntiva**: `bot`, `atom` y `eq` **no inducen**.

## 🔑 Las dos decisiones que la hicieron viable

1. **SACAR EL `∃` FUERA — también de la MAQUINARIA, no sólo del paso.** Toda la fusión de testigos
   (§12-§13) se prueba con los testigos **ABSTRACTOS** y en forma de **implicación OBJETO**
   (`prf_isFC1_binN`, `prf_isFC1_unN`, `prf_hasWitF_imp`): ni un índice De Bruijn que mover. Los
   existenciales se eliminan después y allí cada constructor es **un solo `mp`**.
2. **CADA CASO GENÉRICO EN EL CONTEXTO, con sus hipótesis por ARGUMENTO.** Los ocho casos salen de
   **siete `or`-elim anidados** sobre `isFormCodeE2`: un caso a profundidad `d` vive con `d`
   disyunciones residuales delante, y escribir esos ocho contextos era el grueso del trabajo.

⚠️ **`wfAllF wF wT` NO es monótono en `wF`** (aparece en la cota `lenc wF`), sólo en `wT`. Extender
o fusionar `wF` va por la forma de PERTENENCIA, donde `concat` es axioma (`ax_L3_in_concat`).

⚠️ Al promover: `psi_lift_form4`/`PSI_inst4` subieron a `Meta/StrongInductionPrf.lean` (son
maquinaria genérica de la inducción fuerte) y `PrfH_congr_substfc3` bajó a
`Meta/NumCodeClosedPrf.lean` desde `BdAllIntroPrf` (ADR-019). La familia `PHI…` del sondeo se
renombró a `PHIT…` para no colisionar con las de `EvalLiftcPrf` y `HasWitTcFnPrf`.

**Footprint**: `[propext, Classical.choice, Quot.sound]` — **net-0 puro**.
-/

open FOL
open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.NatArithPrf
open ROBINSON_PlusPlus.Meta.BoundedInPrf
open ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.Sigma1Prf
open ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.NumListPrf
open ROBINSON_PlusPlus.Meta.StrongInductionPrf
open ROBINSON_PlusPlus.Meta.SubstArith
open ROBINSON_PlusPlus.Meta.NumCodeClosedPrf
open ROBINSON_PlusPlus.Meta.CantorMonoPrf
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf.ENS
open ROBINSON_PlusPlus.Meta.HasWitTcFnPrf

set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000

namespace ROBINSON_PlusPlus.Meta.SubstfcWitnessPrf

/-! ## §1 · El predicado de la mitad de LISTA

`hasWit` dice «este CÓDIGO tiene testigo». Para una LISTA de códigos hace falta «todos sus
elementos comparten un testigo», que es la forma que consume el nodo `funcc`. -/

/-- `hasWitArgs Y`: la lista `Y` tiene un testigo COMÚN bien formado. -/
def hasWitArgs (Y : Term) : Formula :=
  Formula.ex (land (wfAll1 (.var 0)) (argsIn (.var 0) (liftTerm 0 Y)))

theorem liftF_hasWitArgs (k : Nat) (Y : Term) :
    liftFormula k (hasWitArgs Y) = hasWitArgs (liftTerm k Y) := by
  simp only [hasWitArgs, land, liftFormula, liftF_wfAll1, liftF_argsIn, liftTerm,
    Nat.zero_lt_succ, reduceIte, ← FOL.liftTerm_comm_zero]

theorem substF_hasWitArgs (v : Nat) (s Y : Term) :
    substFormula v s (hasWitArgs Y) = hasWitArgs (substTerm v s Y) := by
  have hz : (0 = v + 1) = False := eq_false (by omega)
  have hz2 : (0 > v + 1) = False := eq_false (by omega)
  simp only [hasWitArgs, land, substFormula, substF_wfAll1, substF_argsIn, substTerm,
    hz, hz2, if_false, FOL.substTerm_lift_comm_zero]

/-! ## §2 · EL ARMAZÓN de la inducción conjuntiva

`BODY w v s X` es el enunciado con TODO explícito; `PHIT` lo cierra sobre los tres binders.
`#3` es el CÓDIGO sobre el que se induce; `#2` = `w`, `#1` = `v`, `#0` = `s`.

🔑 Los tres binders van DENTRO por el gate `liftFormula 1 Φ = Φ`, y la instanciación se colapsa
**paso a paso** (`PHIT_spec1/2/3`), no con un `simp` final: con tres sustituciones anidadas el
`simp` grande no reduce. Es el patrón de `sondeos/EvalSubstfcPrf.lean:6357`. -/

def BODY (w v s X : Term) : Formula :=
  land (Formula.impl (land (isTC1 w X) (hasWit s)) (hasWit (substtc v s X)))
       (Formula.impl (land (land (wfAll1 w) (argsIn w X)) (hasWit s))
         (hasWitArgs (substtsc v s X)))

theorem liftF_BODY (k : Nat) (w v s X : Term) :
    liftFormula k (BODY w v s X)
      = BODY (liftTerm k w) (liftTerm k v) (liftTerm k s) (liftTerm k X) := by
  simp only [BODY, land, liftFormula, liftF_isTC1, liftF_wfAll1, liftF_argsIn, liftF_hasWit,
    liftF_hasWitArgs, substtc, substtsc, liftTerm, liftTerms]

theorem substF_BODY (k : Nat) (u w v s X : Term) :
    substFormula k u (BODY w v s X)
      = BODY (substTerm k u w) (substTerm k u v) (substTerm k u s) (substTerm k u X) := by
  simp only [BODY, land, substFormula, substF_isTC1, substF_wfAll1, substF_argsIn, substF_hasWit,
    substF_hasWitArgs, substtc, substtsc, substTerm, substTerms]

private def PHITbody : Formula := BODY (.var 2) (.var 1) (.var 0) (.var 3)

def PHIT : Formula := Formula.forall (Formula.forall (Formula.forall PHITbody))

/-- **EL GATE de `prf_strong_induction`.** -/
theorem hPHIT : liftFormula 1 PHIT = PHIT := by
  simp only [PHIT, PHITbody, liftFormula, liftF_BODY, liftTerm, Nat.reduceAdd, Nat.reduceLT,
    reduceIte]

theorem PHIT_at (t : Term) :
    substFormula 0 t PHIT = Formula.forall (Formula.forall (Formula.forall
      (BODY (.var 2) (.var 1) (.var 0)
        (liftTerm 0 (liftTerm 0 (liftTerm 0 t)))))) := by
  simp only [PHIT, PHITbody, substFormula, substF_BODY, substTerm, Nat.reduceAdd,
    Nat.reduceEqDiff, Nat.reduceGT, Nat.reduceSub, reduceIte, if_true]

/-! ### Los tres colapsos, uno por binder -/

theorem PHIT_spec1 (t w : Term) :
    substFormula 0 w (Formula.forall (Formula.forall
      (BODY (.var 2) (.var 1) (.var 0) (liftTerm 0 (liftTerm 0 (liftTerm 0 t))))))
      = Formula.forall (Formula.forall
          (BODY (liftTerm 0 (liftTerm 0 w)) (.var 1) (.var 0)
            (liftTerm 0 (liftTerm 0 t)))) := by
  have h3 := substTerm_liftLiftLift t 0 (liftTerm 0 (liftTerm 0 w))
  simp only [substFormula, substF_BODY, substTerm, Nat.reduceAdd, Nat.reduceEqDiff,
    Nat.reduceGT, Nat.reduceSub, reduceIte, if_true, FOL.substTerm_liftTerm, h3]

theorem PHIT_spec2 (t w v : Term) :
    substFormula 0 v (Formula.forall
      (BODY (liftTerm 0 (liftTerm 0 w)) (.var 1) (.var 0) (liftTerm 0 (liftTerm 0 t))))
      = Formula.forall (BODY (liftTerm 0 w) (liftTerm 0 v) (.var 0) (liftTerm 0 t)) := by
  have hw := FOL.substTerm_liftLift w 0 (liftTerm 0 v)
  have ht := FOL.substTerm_liftLift t 0 (liftTerm 0 v)
  simp only [substFormula, substF_BODY, substTerm, Nat.reduceAdd, Nat.reduceEqDiff,
    Nat.reduceGT, Nat.reduceSub, reduceIte, if_true, FOL.substTerm_liftTerm, hw, ht]

theorem PHIT_spec3 (t w v s : Term) :
    substFormula 0 s (BODY (liftTerm 0 w) (liftTerm 0 v) (.var 0) (liftTerm 0 t))
      = BODY w v s t := by
  simp only [substF_BODY, substTerm, if_true, FOL.substTerm_liftTerm]

/-- Instanciación de los tres binders (`w`, `v`, `s`), en ese orden. -/
theorem PHIT_use {Γ : List Formula} (t w v s : Term) (h : PrfH Γ (substFormula 0 t PHIT)) :
    PrfH Γ (BODY w v s t) := by
  rw [PHIT_at] at h
  have h1 := PrfH_spec h w
  rw [PHIT_spec1] at h1
  have h2 := PrfH_spec h1 v
  rw [PHIT_spec2] at h2
  have h3 := PrfH_spec h2 s
  rwa [PHIT_spec3] at h3

/-! ## §3 · Sobre el paso

Molde: `Meta/EvalLiftcPrf.lean:396` (B2). La diferencia es que allí `PHIT` tiene UN binder y aquí
TRES, así que hay tres `PrfH.gen` y la contabilidad De Bruijn se triplica: dentro del cuerpo el
código pasa a ser `#3` y los binders `#2`/`#1`/`#0`. El paso ENSAMBLADO está en §13, tras los
cuatro casos. -/

/-! ## §4 · Los auxiliares que el paso consume y no existían -/

/-- El testigo VACÍO es bien formado (vacuamente: `lenc nil = 0`). -/
theorem prf_wfAll1_nil : Prf (wfAll1 nil) := by
  refine Prf.gen _ (prf_deduction ?_)
  have hlt : PrfH [lt (.var 0) (liftTerm 0 (lenc nil))] (lt (.var 0) (lenc nil)) :=
    prfH_hyp_self _
  have hz : PrfH [lt (.var 0) (liftTerm 0 (lenc nil))] (lt (.var 0) zero) :=
    ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2 (prf_to_prfH prf_lenc_nil _) hlt
  exact PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.efq _))
    (PrfH.mp _ _ _ (prf_to_prfH (prf_not_lt_zero (.var 0)) _) hz)

/-- **Un código de VARIABLE siempre tiene testigo**: él solo se basta.
    (`prf_isTermCodeE1_var` es incondicional en el testigo — un nodo variable no tiene args.) -/
theorem prf_hasWit_varc (m : Term) : Prf (hasWit (varc m)) := by
  refine prf_ex_intro (cons (varc m) nil) ?_
  have h : substFormula 0 (cons (varc m) nil) (isTC1 (.var 0) (liftTerm 0 (varc m)))
      = isTC1 (cons (varc m) nil) (varc m) := by
    simp only [substF_isTC1, substTerm, if_true, FOL.substTerm_liftTerm]
  rw [h]
  refine prf_and_intro ?_ (prf_in_cons_head _ _)
  exact prf_mp (prf_wfAll1_cons (varc m) nil)
    (prf_and_intro (prf_isTermCodeE1_var (cons (varc m) nil) m) prf_wfAll1_nil)

/-- Tricotomía del orden, en `Prf` (`ax19_lt_trichotomy`). -/
theorem prf_lt_trich (a b : Term) :
    Prf (lor (lt a b) (lor (Formula.eq a b) (lt b a))) := by
  have h := prf_spec (prf_spec
    (prf_ax (show ax19_lt_trichotomy ∈ axioms by simp [axioms])) a) b
  simp [ax19_lt_trichotomy, substFormula, substTerm, substTerms, lt, lor,
    FOL.substTerm_liftTerm] at h
  exact h

/-! ## §5 · EL PASO, mitad TÉRMINO — caso `varc`

`shapeUn X 0` **es** `X ≐ varc (nthc X 1̄)` por definición (`numeralM 0 = zero`), así que el caso
se decide por TRICOTOMÍA sobre `v` y el índice: dos ramas dan un nodo variable (testigo propio,
`prf_hasWit_varc`) y la tercera devuelve `s`, cuyo testigo es la hipótesis. -/

/-- Contexto de la mitad TÉRMINO tras introducir su antecedente. -/
private def CTX1 : List Formula :=
  [land (isTC1 (.var 2) (.var 3)) (hasWit (.var 0)),
   liftFormula 0 (liftFormula 0 (liftFormula 0 (PSI PHIT)))]

/-- El índice de la variable, cuando el código resulta ser un `varc`. -/
private def NN : Term := nthc (.var 3) (numeralM 1)

/-- **El caso `varc`, aislado.** Del `shapeUn` y las hipótesis sale el testigo del sustituido. -/
private theorem caso_varc :
    PrfH (shapeUn (.var 3) 0 :: CTX1) (hasWit (substtc (.var 1) (.var 0) (.var 3))) := by
  have hshape : PrfH (shapeUn (.var 3) 0 :: CTX1) (shapeUn (.var 3) 0) :=
    PrfH.hyp _ _ (List.Mem.head _)
  have hsub : PrfH (shapeUn (.var 3) 0 :: CTX1)
      (substtc (.var 1) (.var 0) (.var 3) =eq substtc (.var 1) (.var 0) (varc NN)) :=
    PrfH_congr_substtc3 hshape
  refine PrfH_or_elim (prf_to_prfH (prf_lt_trich (.var 1) NN) _) ?c_lt ?c_rest
  case c_lt =>
    have hlt : PrfH (lt (.var 1) NN :: shapeUn (.var 3) 0 :: CTX1) (lt (.var 1) NN) :=
      PrfH.hyp _ _ (List.Mem.head _)
    have hs2 : PrfH (lt (.var 1) NN :: shapeUn (.var 3) 0 :: CTX1)
        (substtc (.var 1) (.var 0) (.var 3) =eq substtc (.var 1) (.var 0) (varc NN)) :=
      PrfH_congr_substtc3 (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))
    have heq := PrfH.mp _ _ _
      (prf_to_prfH (prf_substtc_var_gt (.var 1) (.var 0) NN) _) hlt
    exact PrfH_congr_hasWit (PrfH_eq_symm (PrfH_eq_trans hs2 heq))
      (prf_to_prfH (prf_hasWit_varc (pred NN)) _)
  case c_rest =>
    refine PrfH_or_elim (PrfH.hyp _ _ (List.Mem.head _)) ?c_eq ?c_gt
    case c_eq =>
      have heq0 : PrfH (Formula.eq (.var 1) NN ::
          lor (Formula.eq (.var 1) NN) (lt NN (.var 1)) :: shapeUn (.var 3) 0 :: CTX1)
          (Formula.eq (.var 1) NN) := PrfH.hyp _ _ (List.Mem.head _)
      have hs2 : PrfH (Formula.eq (.var 1) NN ::
          lor (Formula.eq (.var 1) NN) (lt NN (.var 1)) :: shapeUn (.var 3) 0 :: CTX1)
          (substtc (.var 1) (.var 0) (.var 3) =eq substtc (.var 1) (.var 0) (varc NN)) :=
        PrfH_congr_substtc3 (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
      have hws : PrfH (Formula.eq (.var 1) NN ::
          lor (Formula.eq (.var 1) NN) (lt NN (.var 1)) :: shapeUn (.var 3) 0 :: CTX1)
          (hasWit (.var 0)) :=
        PrfH_and_elim_right (PrfH.hyp _ _
          (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
      have heq := PrfH.mp _ _ _
        (prf_to_prfH (prf_substtc_var_eq (.var 1) (.var 0) NN) _) heq0
      exact PrfH_congr_hasWit (PrfH_eq_symm (PrfH_eq_trans hs2 heq)) hws
    case c_gt =>
      have hgt : PrfH (lt NN (.var 1) ::
          lor (Formula.eq (.var 1) NN) (lt NN (.var 1)) :: shapeUn (.var 3) 0 :: CTX1)
          (lt NN (.var 1)) := PrfH.hyp _ _ (List.Mem.head _)
      have hs2 : PrfH (lt NN (.var 1) ::
          lor (Formula.eq (.var 1) NN) (lt NN (.var 1)) :: shapeUn (.var 3) 0 :: CTX1)
          (substtc (.var 1) (.var 0) (.var 3) =eq substtc (.var 1) (.var 0) (varc NN)) :=
        PrfH_congr_substtc3 (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
      have heq := PrfH.mp _ _ _
        (prf_to_prfH (prf_substtc_var_lt (.var 1) (.var 0) NN) _) hgt
      exact PrfH_congr_hasWit (PrfH_eq_symm (PrfH_eq_trans hs2 heq))
        (prf_to_prfH (prf_hasWit_varc NN) _)

/-! ## §6 · Dos piezas reutilizables para el caso `funcc`

`prf_isTermCodeE1_func` pide su `argsIn` como hipótesis **META**; dentro del paso llega por el
contexto `PrfH`, así que hace falta la versión en implicación OBJETO — la moneda de §3.31.
Con ella, «un nodo funcional cuyos argumentos comparten testigo tiene testigo» sale limpio. -/

theorem prf_isTermCodeE1_func_imp (W S C : Term) :
    Prf (Formula.impl (argsIn W C) (isTermCodeE1 W (funcc S C))) := by
  unfold isTermCodeE1
  refine prf_deduction ?_
  have hargs : PrfH [argsIn W C] (argsIn W C) := prfH_hyp_self _
  refine PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.j2 _ _)) ?_
  refine PrfH.mp _ _ _ (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.c1 _ _)) ?shape) ?args
  case shape =>
    exact prf_to_prfH (prf_eq_symm (prf_congr_cons_tail (prf_eq_trans
      (prf_congr_cons_head (prf_nthc_c1 (numeralM 1) S (cons C nil)))
      (prf_congr_cons_tail (prf_congr_cons_head (prf_nthc_c2 (numeralM 1) S C nil)))))) _
  case args =>
    exact PrfH_congr_argsIn
      (prf_to_prfH (prf_eq_symm (prf_nthc_c2 (numeralM 1) S C nil)) _) hargs

/-- **Un nodo funcional cuyos argumentos comparten testigo, tiene testigo.**
    El `∃` se elimina aquí, a nivel `Prf` (`prf_ex_elim_imp`), que es mucho más barato que
    hacerlo dentro del paso con `PrfH_ex_elim` y su doble lift. -/
theorem prf_hasWit_funcc (S Y : Term) :
    Prf (Formula.impl (hasWitArgs Y) (hasWit (funcc S Y))) := by
  refine prf_ex_elim_imp ?_
  have hgoal : liftFormula 0 (hasWit (funcc S Y))
      = hasWit (funcc (liftTerm 0 S) (liftTerm 0 Y)) := by
    simp only [liftF_hasWit, funcc, cons, succ, zero, nil, liftTerm, liftTerms]
  rw [hgoal]
  have hctx : PrfH [land (wfAll1 (.var 0)) (argsIn (.var 0) (liftTerm 0 Y))]
      (land (wfAll1 (.var 0)) (argsIn (.var 0) (liftTerm 0 Y))) := prfH_hyp_self _
  have hwf := PrfH_and_elim_left hctx
  have hargs := PrfH_and_elim_right hctx
  -- el nodo, y su testigo: `cons nodo w`
  have hnode : PrfH [land (wfAll1 (.var 0)) (argsIn (.var 0) (liftTerm 0 Y))]
      (isTermCodeE1 (cons (funcc (liftTerm 0 S) (liftTerm 0 Y)) (.var 0))
        (funcc (liftTerm 0 S) (liftTerm 0 Y))) := by
    refine PrfH.mp _ _ _ (prf_to_prfH (prf_isTermCodeE1_func_imp
      (cons (funcc (liftTerm 0 S) (liftTerm 0 Y)) (.var 0))
      (liftTerm 0 S) (liftTerm 0 Y)) _) ?_
    exact PrfH.mp _ _ _ (prf_to_prfH (prf_argsIn_mono
      (funcc (liftTerm 0 S) (liftTerm 0 Y)) (.var 0) (liftTerm 0 Y)) _) hargs
  have hwf' : PrfH [land (wfAll1 (.var 0)) (argsIn (.var 0) (liftTerm 0 Y))]
      (wfAll1 (cons (funcc (liftTerm 0 S) (liftTerm 0 Y)) (.var 0))) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_wfAll1_cons
      (funcc (liftTerm 0 S) (liftTerm 0 Y)) (.var 0)) _) (PrfH_and_intro hnode hwf)
  refine PrfH_ex_intro (cons (funcc (liftTerm 0 S) (liftTerm 0 Y)) (.var 0)) ?_
  have hs : substFormula 0 (cons (funcc (liftTerm 0 S) (liftTerm 0 Y)) (.var 0))
      (isTC1 (.var 0) (liftTerm 0 (funcc (liftTerm 0 S) (liftTerm 0 Y))))
      = isTC1 (cons (funcc (liftTerm 0 S) (liftTerm 0 Y)) (.var 0))
          (funcc (liftTerm 0 S) (liftTerm 0 Y)) := by
    simp only [substF_isTC1, substTerm, if_true, FOL.substTerm_liftTerm]
  rw [hs]
  exact PrfH_and_intro hwf' (prf_to_prfH (prf_in_cons_head _ _) _)

/-! ## §7 · EL PASO, mitad TÉRMINO — caso `funcc`

Baja al argumento por la **cadena de Cantor** (`AA < ⟨AA⟩ < ⟨SS,AA⟩ < ⟨1̄,SS,AA⟩ = X`), aplica la
hipótesis de inducción con `PSI_inst3` —**tres** lifts, porque `PHIT` tiene tres binders; la
escalera psi que B3 promovió— y monta el nodo sustituido con §6. -/

/-- El símbolo y los argumentos, cuando el código resulta ser un `funcc`. -/
private def SS : Term := nthc (.var 3) (numeralM 1)
private def AA : Term := nthc (.var 3) (numeralM 2)

private theorem caso_funcc :
    PrfH (land (shapeBin (.var 3) 1) (argsIn (.var 2) AA) :: CTX1)
      (hasWit (substtc (.var 1) (.var 0) (.var 3))) := by
  have hb : PrfH (land (shapeBin (.var 3) 1) (argsIn (.var 2) AA) :: CTX1)
      (land (shapeBin (.var 3) 1) (argsIn (.var 2) AA)) := PrfH.hyp _ _ (List.Mem.head _)
  have hshape := PrfH_and_elim_left hb
  have hargs := PrfH_and_elim_right hb
  have hh : PrfH (land (shapeBin (.var 3) 1) (argsIn (.var 2) AA) :: CTX1)
      (land (isTC1 (.var 2) (.var 3)) (hasWit (.var 0))) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hwf := PrfH_and_elim_left (PrfH_and_elim_left hh)
  have hws := PrfH_and_elim_right hh
  have hpsi : PrfH (land (shapeBin (.var 3) 1) (argsIn (.var 2) AA) :: CTX1)
      (liftFormula 0 (liftFormula 0 (liftFormula 0 (PSI PHIT)))) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  -- (1) la CADENA DE CANTOR: el argumento es estrictamente menor que el nodo
  have h1 : Prf (lt AA (cons AA nil)) := prf_cantor_mono_left _ _
  have h2 : Prf (lt (cons AA nil) (cons SS (cons AA nil))) := prf_cantor_mono_right _ _
  have h3 : Prf (lt (cons SS (cons AA nil))
      (cons (numeralM 1) (cons SS (cons AA nil)))) := prf_cantor_mono_right _ _
  have h12 : Prf (lt AA (cons SS (cons AA nil))) :=
    prf_mp (prf_mp (prf_lt_trans _ _ _) h1) h2
  have h123 : Prf (lt AA (cons (numeralM 1) (cons SS (cons AA nil)))) :=
    prf_mp (prf_mp (prf_lt_trans _ _ _) h12) h3
  have hltb := ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2
    (PrfH_eq_symm hshape) (prf_to_prfH h123 _)
  -- (2) la HIPOTESIS DE INDUCCION en el argumento
  have hih := PrfH.mp _ _ _ (PSI_inst3 PHIT hPHIT hpsi AA) hltb
  have huse := PHIT_use AA (.var 2) (.var 1) (.var 0) hih
  have hargsW := PrfH.mp _ _ _ (PrfH_and_elim_right huse)
    (PrfH_and_intro (PrfH_and_intro hwf hargs) hws)
  -- (3) el nodo sustituido tiene testigo (§6)
  have hnode := PrfH.mp _ _ _
    (prf_to_prfH (prf_hasWit_funcc SS (substtsc (.var 1) (.var 0) AA)) _) hargsW
  -- (4) y se transporta al codigo original
  have hs1 : PrfH (land (shapeBin (.var 3) 1) (argsIn (.var 2) AA) :: CTX1)
      (substtc (.var 1) (.var 0) (.var 3) =eq substtc (.var 1) (.var 0) (funcc SS AA)) :=
    PrfH_congr_substtc3 hshape
  have hs2 : PrfH (land (shapeBin (.var 3) 1) (argsIn (.var 2) AA) :: CTX1)
      (substtc (.var 1) (.var 0) (funcc SS AA)
        =eq funcc SS (substtsc (.var 1) (.var 0) AA)) :=
    prf_to_prfH (prf_substtc_func (.var 1) (.var 0) SS AA) _
  exact PrfH_congr_hasWit (PrfH_eq_symm (PrfH_eq_trans hs1 hs2)) hnode

/-! ## §8 · La mitad de LISTA — sus piezas

⚠️ `prf_nil_or_cons` vive en `Meta/EvalLiftcPrf.lean`, que hoy está **en rojo** (aguas abajo de
`MpCodePrf`) y no se puede importar. Se reproduce aquí: `prf_list_induction` está en `ChainPrf`,
que sí compila, y el paso **no usa la hipótesis de inducción**. -/

def nilOrCons : Formula := lor (Formula.eq (.var 0) nil) (consOk (.var 0))

theorem nilOrCons_at (Y : Term) :
    substFormula 0 Y nilOrCons = lor (Formula.eq Y nil) (consOk Y) := by
  simp only [nilOrCons, consOk, lor, carc, cdrc, cons, nil, zero, substFormula, substTerm,
    substTerms, if_true]

theorem prf_nil_or_cons_all : Prf (Formula.forall nilOrCons) := by
  refine prf_list_induction nilOrCons ?base ?step
  · rw [nilOrCons_at]
    exact prf_orL (prf_refl nil)
  · refine Prf.gen _ (Prf.gen _ ?_)
    have hR : substFormula 0 (cons (.var 1) (.var 0)) (liftFormula 2 (liftFormula 1 nilOrCons))
        = lor (Formula.eq (cons (.var 1) (.var 0)) nil) (consOk (cons (.var 1) (.var 0))) := by
      simp only [nilOrCons, consOk, lor, carc, cdrc, cons, nil, zero, liftFormula, substFormula,
        liftTerm, liftTerms, substTerm, substTerms, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceGT,
        reduceIte, if_true]
    rw [hR]
    exact prf_mp (Prf.incl (Prf₀.p1 _ _)) (prf_orR (prf_consOk_cons _ _))

theorem prf_nil_or_cons (Y : Term) : Prf (lor (Formula.eq Y nil) (consOk Y)) := by
  have h := prf_spec prf_nil_or_cons_all Y
  rwa [nilOrCons_at] at h

/-- `argsIn W nil` es VACUO (`lenc nil = 0`). -/
theorem prf_argsIn_nil (W : Term) : Prf (argsIn W nil) := by
  refine Prf.gen _ (prf_deduction ?_)
  have hlt : PrfH [lt (.var 0) (liftTerm 0 (lenc nil))] (lt (.var 0) (lenc nil)) :=
    prfH_hyp_self _
  have hz : PrfH [lt (.var 0) (liftTerm 0 (lenc nil))] (lt (.var 0) zero) :=
    ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2 (prf_to_prfH prf_lenc_nil _) hlt
  exact PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.efq _))
    (PrfH.mp _ _ _ (prf_to_prfH (prf_not_lt_zero (.var 0)) _) hz)

/-- Contexto del `∀` acotado de la introducción de `argsIn`. -/
private def CTXa (W a as : Term) : List Formula :=
  [lt (.var 0) (lenc (cons (liftTerm 0 a) (liftTerm 0 as))),
   land (In (liftTerm 0 a) (liftTerm 0 W)) (argsIn (liftTerm 0 W) (liftTerm 0 as))]

/-- **INTRODUCCIÓN de `argsIn` sobre `cons`**: cabeza en el testigo + cola ya cubierta.
    Misma estructura que `prf_wfAll1_cons`: corte del índice con `prf_zero_or_eq_succ_pred`. -/
theorem prf_argsIn_cons_intro (W a as : Term) :
    Prf (Formula.impl (land (In a W) (argsIn W as)) (argsIn W (cons a as))) := by
  refine prf_mp (Prf.qconf (land (In a W) (argsIn W as)) (argsInBody W (cons a as)))
    (Prf.gen _ ?_)
  simp only [liftFormula, liftF_argsIn, land, In, liftTerm, liftTerms]
  refine prf_deduction (deduction_aux ?_
    (lt (.var 0) (liftTerm 0 (lenc (cons a as))))
    [land (In (liftTerm 0 a) (liftTerm 0 W)) (argsIn (liftTerm 0 W) (liftTerm 0 as))] rfl)
  refine PrfH_or_elim (prf_to_prfH (prf_zero_or_eq_succ_pred (.var 0)) _) ?zc ?sc
  case zc =>
    have hz : PrfH (Formula.eq (.var 0) zero :: CTXa W a as) (Formula.eq (.var 0) zero) :=
      PrfH.hyp _ _ (List.Mem.head _)
    have hin : PrfH (Formula.eq (.var 0) zero :: CTXa W a as)
        (In (liftTerm 0 a) (liftTerm 0 W)) :=
      PrfH_and_elim_left (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
    have hnth : PrfH (Formula.eq (.var 0) zero :: CTXa W a as)
        (nthc (cons (liftTerm 0 a) (liftTerm 0 as)) (.var 0) =eq liftTerm 0 a) :=
      PrfH_eq_trans (PrfH_congr_nthc_idx _ hz)
        (prf_to_prfH (prf_nthc_zero (liftTerm 0 a) (liftTerm 0 as)) _)
    exact PrfH_congr_In_left (PrfH_eq_symm hnth) hin
  case sc =>
    have hs : PrfH (Formula.eq (.var 0) (succ (pred (.var 0))) :: CTXa W a as)
        (Formula.eq (.var 0) (succ (pred (.var 0)))) := PrfH.hyp _ _ (List.Mem.head _)
    have hlt2 : PrfH (Formula.eq (.var 0) (succ (pred (.var 0))) :: CTXa W a as)
        (lt (.var 0) (lenc (cons (liftTerm 0 a) (liftTerm 0 as)))) :=
      PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
    have hargs : PrfH (Formula.eq (.var 0) (succ (pred (.var 0))) :: CTXa W a as)
        (argsIn (liftTerm 0 W) (liftTerm 0 as)) :=
      PrfH_and_elim_right (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
    have hltS : PrfH (Formula.eq (.var 0) (succ (pred (.var 0))) :: CTXa W a as)
        (lt (succ (pred (.var 0))) (succ (lenc (liftTerm 0 as)))) :=
      ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2
        (prf_to_prfH (prf_lenc_cons (liftTerm 0 a) (liftTerm 0 as)) _)
        (ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst1 hs hlt2)
    have hltw : PrfH (Formula.eq (.var 0) (succ (pred (.var 0))) :: CTXa W a as)
        (lt (pred (.var 0)) (lenc (liftTerm 0 as))) :=
      PrfH.mp _ _ _ (prf_to_prfH
        (prf_lt_of_succ_lt_succ (pred (.var 0)) (lenc (liftTerm 0 as))) _) hltS
    have hin : PrfH (Formula.eq (.var 0) (succ (pred (.var 0))) :: CTXa W a as)
        (In (nthc (liftTerm 0 as) (pred (.var 0))) (liftTerm 0 W)) :=
      PrfH.mp _ _ _ (PrfH_inst_argsIn (liftTerm 0 W) (liftTerm 0 as)
        (pred (.var 0)) hargs) hltw
    have hnth : PrfH (Formula.eq (.var 0) (succ (pred (.var 0))) :: CTXa W a as)
        (nthc (cons (liftTerm 0 a) (liftTerm 0 as)) (.var 0)
          =eq nthc (liftTerm 0 as) (pred (.var 0))) :=
      PrfH_eq_trans (PrfH_congr_nthc_idx _ hs)
        (prf_to_prfH (prf_nthc_succ (liftTerm 0 a) (liftTerm 0 as) (pred (.var 0))) _)
    exact PrfH_congr_In_left (PrfH_eq_symm hnth) hin

/-! ## §9 · Congruencias que faltaban, y el caso `nil` -/

theorem PrfH_congr_substtsc3 {Γ : List Formula} {v s a b : Term} (h : PrfH Γ (a =eq b)) :
    PrfH Γ (substtsc v s a =eq substtsc v s b) := by
  let f : Formula := Formula.eq (substtsc (liftTerm 0 v) (liftTerm 0 s) (liftTerm 0 a))
                                (substtsc (liftTerm 0 v) (liftTerm 0 s) (.var 0))
  have hS : ∀ x : Term, substFormula 0 x f
      = Formula.eq (substtsc v s a) (substtsc v s x) := by
    intro x
    simp only [f, substtsc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS b) ▸ ROBINSON_PlusPlus.Meta.ChainPrf.PrfH_leibniz_subst (A := f) h
    ((hS a) ▸ prf_to_prfH (prf_refl (substtsc v s a)) _)

theorem PrfH_congr_hasWitArgs {Γ : List Formula} {a b : Term}
    (h : PrfH Γ (a =eq b)) (hw : PrfH Γ (hasWitArgs a)) : PrfH Γ (hasWitArgs b) := by
  have e : ∀ x : Term, substFormula 0 x (hasWitArgs (.var 0)) = hasWitArgs x := by
    intro x; simp only [substF_hasWitArgs, substTerm, if_true]
  exact (e b) ▸ ROBINSON_PlusPlus.Meta.ChainPrf.PrfH_leibniz_subst
    (A := hasWitArgs (.var 0)) h ((e a) ▸ hw)

/-- La lista VACÍA tiene testigo (el vacío). -/
theorem prf_hasWitArgs_nil : Prf (hasWitArgs nil) := by
  refine prf_ex_intro nil ?_
  have h : substFormula 0 nil (land (wfAll1 (.var 0)) (argsIn (.var 0) (liftTerm 0 nil)))
      = land (wfAll1 nil) (argsIn nil nil) := by
    simp only [land, substFormula, substF_wfAll1, substF_argsIn, substTerm, substTerms,
      if_true, FOL.substTerm_liftTerm]
  rw [h]
  exact prf_and_intro prf_wfAll1_nil (prf_argsIn_nil nil)

/-- Contexto de la mitad LISTA tras introducir su antecedente. -/
private def CTX2 : List Formula :=
  [land (land (wfAll1 (.var 2)) (argsIn (.var 2) (.var 3))) (hasWit (.var 0)),
   liftFormula 0 (liftFormula 0 (liftFormula 0 (PSI PHIT)))]

/-- **El caso `nil` de la mitad de LISTA.** -/
private theorem caso_nil :
    PrfH (Formula.eq (.var 3) nil :: CTX2) (hasWitArgs (substtsc (.var 1) (.var 0) (.var 3))) := by
  have heq : PrfH (Formula.eq (.var 3) nil :: CTX2) (Formula.eq (.var 3) nil) :=
    PrfH.hyp _ _ (List.Mem.head _)
  have h1 : PrfH (Formula.eq (.var 3) nil :: CTX2)
      (substtsc (.var 1) (.var 0) (.var 3) =eq substtsc (.var 1) (.var 0) nil) :=
    PrfH_congr_substtsc3 heq
  have h2 : PrfH (Formula.eq (.var 3) nil :: CTX2)
      (substtsc (.var 1) (.var 0) nil =eq nil) :=
    prf_to_prfH (prf_substtsc_nil (.var 1) (.var 0)) _
  exact PrfH_congr_hasWitArgs (PrfH_eq_symm (PrfH_eq_trans h1 h2))
    (prf_to_prfH prf_hasWitArgs_nil _)

/-! ## §10 · LA FUSIÓN DE TESTIGOS — copiada de `sondeos/MergeTestigos.lean` (TAREA A)

⚠️ Se COPIA porque `sondeos/` está fuera del build y no es importable. Al promover, esto queda
como una sola constante; aquí es la duplicación normal entre sondeos.

🔑 Es lo que el caso `cons` necesita y no existía: la HI da un testigo para la CABEZA y otro para
la COLA, y hay que fusionarlos. La ruta es pasar a forma de PERTENENCIA (donde `concat` es un
axioma), fusionar allí, y volver: ni un índice partido. -/

theorem prf_in_nthc (L i : Term) :
    Prf (Formula.impl (lt i (lenc L)) (In (nthc L i) L)) := by
  refine prf_deduction ?_
  have hlt : PrfH [lt i (lenc L)] (lt i (lenc L)) := prfH_hyp_self _
  have hsub : substFormula 0 i (land (lt (.var 0) (liftTerm 0 (lenc L)))
      (Formula.eq (nthc (liftTerm 0 L) (.var 0)) (liftTerm 0 (nthc L i))))
      = land (lt i (lenc L)) (Formula.eq (nthc L i) (nthc L i)) := by
    simp only [land, lt, lenc, nthc, In, substFormula, substTerm, substTerms,
      FOL.substTerm_liftTerm, if_true]
  have hb : PrfH [lt i (lenc L)] (boundedIn (nthc L i) L) := by
    unfold boundedIn
    refine PrfH_ex_intro i ?_
    rw [hsub]
    exact PrfH.mp _ _ _ (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.c1 _ _)) hlt)
      (prf_to_prfH (prf_refl (nthc L i)) _)
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_In_of_boundedIn (nthc L i) L) _) hb

/-! ## §2 · La monotonía, GENERALIZADA a cualquier inclusión de testigos

`prf_argsIn_mono` (ayer) estaba clavada a `cons a w`. El testigo sólo entra por `In`, así que la
hipótesis honesta es **la inclusión como implicación objeto**. La hipótesis se pide ya LIFTEADA
porque es la forma en que el `∀` acotado la consume. -/

theorem prf_argsIn_mono_of (w w' Y : Term)
    (hsub : ∀ x : Term, Prf (Formula.impl (In x (liftTerm 0 w)) (In x (liftTerm 0 w')))) :
    Prf (Formula.impl (argsIn w Y) (argsIn w' Y)) := by
  refine prf_mp (Prf.qconf (argsIn w Y) (argsInBody w' Y)) (Prf.gen _ ?_)
  rw [liftF_argsIn]
  refine prf_deduction (deduction_aux ?_ (lt (.var 0) (liftTerm 0 (lenc Y)))
    [argsIn (liftTerm 0 w) (liftTerm 0 Y)] rfl)
  show PrfH [lt (.var 0) (lenc (liftTerm 0 Y)), argsIn (liftTerm 0 w) (liftTerm 0 Y)]
    (In (nthc (liftTerm 0 Y) (.var 0)) (liftTerm 0 w'))
  have hlt : PrfH [lt (.var 0) (lenc (liftTerm 0 Y)), argsIn (liftTerm 0 w) (liftTerm 0 Y)]
      (lt (.var 0) (lenc (liftTerm 0 Y))) := PrfH.hyp _ _ (List.Mem.head _)
  have hargs : PrfH [lt (.var 0) (lenc (liftTerm 0 Y)), argsIn (liftTerm 0 w) (liftTerm 0 Y)]
      (argsIn (liftTerm 0 w) (liftTerm 0 Y)) := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hin := PrfH.mp _ _ _
    (PrfH_inst_argsIn (liftTerm 0 w) (liftTerm 0 Y) (.var 0) hargs) hlt
  exact PrfH.mp _ _ _ (prf_to_prfH (hsub (nthc (liftTerm 0 Y) (.var 0))) _) hin

theorem prf_isTermCodeE1_mono_of (w w' X : Term)
    (hsub : ∀ x : Term, Prf (Formula.impl (In x (liftTerm 0 w)) (In x (liftTerm 0 w')))) :
    Prf (Formula.impl (isTermCodeE1 w X) (isTermCodeE1 w' X)) := by
  unfold isTermCodeE1
  refine prf_or_elim_imp ?_ ?_
  · exact Prf.incl (Prf₀.j1 _ _)
  · refine prf_deduction ?_
    have hh : PrfH [land (shapeBin X 1) (argsIn w (nthc X (numeralM 2)))]
        (land (shapeBin X 1) (argsIn w (nthc X (numeralM 2)))) := prfH_hyp_self _
    have h1 := PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.c2 _ _)) hh
    have h2 := PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.c3 _ _)) hh
    have h2' := PrfH.mp _ _ _
      (prf_to_prfH (prf_argsIn_mono_of w w' (nthc X (numeralM 2)) hsub) _) h2
    exact PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.j2 _ _))
      (PrfH.mp _ _ _ (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.c1 _ _)) h1) h2')

/-! ## §3 · LA FUSIÓN

`In` sobre `concat` es un axioma (`ax_L3_in_concat`), así que en forma de pertenencia el caso
sale por `or_elim` sobre las dos mitades. Ni un índice partido. -/

/-- `ax_L3_in_concat` instanciado, en `Prf`. -/
theorem prf_in_concat (x L M : Term) :
    Prf (In x (concat L M) ⇔ lor (In x L) (In x M)) := by
  have h := prf_spec (prf_spec (prf_spec
    (prf_ax (show ax_L3_in_concat ∈ axioms by simp [axioms])) x) L) M
  simp [ax_L3_in_concat, substFormula, substTerm, substTerms, In, concat, lor, iff,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at h
  exact h

/-- Contexto del `∀` acotado de la fusión. -/
private def CTXc (W₁ W₂ : Term) : List Formula :=
  [lt (.var 0) (lenc (concat (liftTerm 0 W₁) (liftTerm 0 W₂))),
   land (wfAll1 (liftTerm 0 W₁)) (wfAll1 (liftTerm 0 W₂))]

/-- 🏁 **LA FUSIÓN**: dos testigos bien formados dan uno bien formado. -/
theorem prf_wfAll1_concat (W₁ W₂ : Term) :
    Prf (Formula.impl (land (wfAll1 W₁) (wfAll1 W₂)) (wfAll1 (concat W₁ W₂))) := by
  refine prf_mp (Prf.qconf (land (wfAll1 W₁) (wfAll1 W₂)) (wfAll1Body (concat W₁ W₂)))
    (Prf.gen _ ?_)
  simp only [liftFormula, liftF_wfAll1, land]
  refine prf_deduction (deduction_aux ?_
    (lt (.var 0) (liftTerm 0 (lenc (concat W₁ W₂))))
    [land (wfAll1 (liftTerm 0 W₁)) (wfAll1 (liftTerm 0 W₂))] rfl)
  have hlt : PrfH (CTXc W₁ W₂)
      (lt (.var 0) (lenc (concat (liftTerm 0 W₁) (liftTerm 0 W₂)))) :=
    PrfH.hyp _ _ (List.Mem.head _)
  -- (1) lo que está en una posición válida, PERTENECE al concat
  have hinC : PrfH (CTXc W₁ W₂)
      (In (nthc (concat (liftTerm 0 W₁) (liftTerm 0 W₂)) (.var 0))
        (concat (liftTerm 0 W₁) (liftTerm 0 W₂))) :=
    PrfH.mp _ _ _ (prf_to_prfH
      (prf_in_nthc (concat (liftTerm 0 W₁) (liftTerm 0 W₂)) (.var 0)) _) hlt
  -- (2) y `In` sobre `concat` SE PARTE — aquí no hay ningún índice que romper
  have hor : PrfH (CTXc W₁ W₂)
      (lor (In (nthc (concat (liftTerm 0 W₁) (liftTerm 0 W₂)) (.var 0)) (liftTerm 0 W₁))
           (In (nthc (concat (liftTerm 0 W₁) (liftTerm 0 W₂)) (.var 0)) (liftTerm 0 W₂))) :=
    PrfH.mp _ _ _ (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.c2 _ _))
      (prf_to_prfH (prf_in_concat (nthc (concat (liftTerm 0 W₁) (liftTerm 0 W₂)) (.var 0))
        (liftTerm 0 W₁) (liftTerm 0 W₂)) _)) hinC
  refine PrfH_or_elim hor ?iz ?dr
  case iz =>
    have hin : PrfH (In (nthc (concat (liftTerm 0 W₁) (liftTerm 0 W₂)) (.var 0))
          (liftTerm 0 W₁) :: CTXc W₁ W₂)
        (In (nthc (concat (liftTerm 0 W₁) (liftTerm 0 W₂)) (.var 0)) (liftTerm 0 W₁)) :=
      PrfH.hyp _ _ (List.Mem.head _)
    have hand : PrfH (In (nthc (concat (liftTerm 0 W₁) (liftTerm 0 W₂)) (.var 0))
          (liftTerm 0 W₁) :: CTXc W₁ W₂)
        (land (wfAll1 (liftTerm 0 W₁)) (wfAll1 (liftTerm 0 W₂))) :=
      PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    have hw1 := PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.c2 _ _)) hand
    have hnode := PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH
      (prf_isTermCodeE1_of_In (liftTerm 0 W₁)
        (nthc (concat (liftTerm 0 W₁) (liftTerm 0 W₂)) (.var 0))) _) hin) hw1
    exact PrfH.mp _ _ _ (prf_to_prfH (prf_isTermCodeE1_mono_of (liftTerm 0 W₁)
      (concat (liftTerm 0 W₁) (liftTerm 0 W₂))
      (nthc (concat (liftTerm 0 W₁) (liftTerm 0 W₂)) (.var 0))
      (fun x => prf_In_mono_right_imp x (liftTerm 0 (liftTerm 0 W₂))
        (liftTerm 0 (liftTerm 0 W₁)))) _) hnode
  case dr =>
    have hin : PrfH (In (nthc (concat (liftTerm 0 W₁) (liftTerm 0 W₂)) (.var 0))
          (liftTerm 0 W₂) :: CTXc W₁ W₂)
        (In (nthc (concat (liftTerm 0 W₁) (liftTerm 0 W₂)) (.var 0)) (liftTerm 0 W₂)) :=
      PrfH.hyp _ _ (List.Mem.head _)
    have hand : PrfH (In (nthc (concat (liftTerm 0 W₁) (liftTerm 0 W₂)) (.var 0))
          (liftTerm 0 W₂) :: CTXc W₁ W₂)
        (land (wfAll1 (liftTerm 0 W₁)) (wfAll1 (liftTerm 0 W₂))) :=
      PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    have hw2 := PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.c3 _ _)) hand
    have hnode := PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH
      (prf_isTermCodeE1_of_In (liftTerm 0 W₂)
        (nthc (concat (liftTerm 0 W₁) (liftTerm 0 W₂)) (.var 0))) _) hin) hw2
    exact PrfH.mp _ _ _ (prf_to_prfH (prf_isTermCodeE1_mono_of (liftTerm 0 W₂)
      (concat (liftTerm 0 W₁) (liftTerm 0 W₂))
      (nthc (concat (liftTerm 0 W₁) (liftTerm 0 W₂)) (.var 0))
      (fun x => prf_In_mono_imp x (liftTerm 0 (liftTerm 0 W₂))
        (liftTerm 0 (liftTerm 0 W₁)))) _) hnode


/-! ## §11 · «cabeza con testigo + cola con testigo ⟹ la lista tiene testigo»

**Donde la TAREA A paga.** Las dos hipótesis son `∃`, así que se eliminan las dos —a nivel `Prf`,
que es más barato que dentro del paso—, y el testigo de la lista es el `concat` de los dos:
`prf_wfAll1_concat` para la buena formación, y la monotonía generalizada para que cada mitad
siga cubriendo lo suyo. -/

theorem prf_hasWitArgs_cons (a as : Term) :
    Prf (Formula.impl (hasWit a) (Formula.impl (hasWitArgs as) (hasWitArgs (cons a as)))) := by
  refine prf_ex_elim_imp ?_
  have hg1 : liftFormula 0 (Formula.impl (hasWitArgs as) (hasWitArgs (cons a as)))
      = Formula.impl (hasWitArgs (liftTerm 0 as))
          (hasWitArgs (cons (liftTerm 0 a) (liftTerm 0 as))) := by
    simp only [liftFormula, liftF_hasWitArgs, cons, liftTerm, liftTerms]
  rw [hg1]
  refine deduction_aux ?_ (hasWitArgs (liftTerm 0 as)) [isTC1 (.var 0) (liftTerm 0 a)] rfl
  -- segunda eliminacion: el testigo de la COLA
  refine PrfH_ex_elim (PrfH.hyp _ _ (List.Mem.head _)) ?_
  simp only [List.map_cons, List.map_nil, liftF_hasWitArgs, liftF_isTC1]
  have hg2 : liftTerm 0 (cons (liftTerm 0 a) (liftTerm 0 as))
      = cons (liftTerm 0 (liftTerm 0 a)) (liftTerm 0 (liftTerm 0 as)) := by
    simp only [cons, liftTerm, liftTerms]
  rw [hg2]
  -- los DOS testigos: `#1` (cabeza, lifteado por la 2a eliminacion) y `#0` (cola)
  have hW1 : PrfH [land (wfAll1 (.var 0)) (argsIn (.var 0) (liftTerm 0 (liftTerm 0 as))),
      hasWitArgs (liftTerm 0 (liftTerm 0 as)),
      isTC1 (liftTerm 0 (.var 0)) (liftTerm 0 (liftTerm 0 a))]
      (isTC1 (.var 1) (liftTerm 0 (liftTerm 0 a))) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  have hW2 : PrfH [land (wfAll1 (.var 0)) (argsIn (.var 0) (liftTerm 0 (liftTerm 0 as))),
      hasWitArgs (liftTerm 0 (liftTerm 0 as)),
      isTC1 (liftTerm 0 (.var 0)) (liftTerm 0 (liftTerm 0 a))]
      (land (wfAll1 (.var 0)) (argsIn (.var 0) (liftTerm 0 (liftTerm 0 as)))) :=
    PrfH.hyp _ _ (List.Mem.head _)
  have hwf1 := PrfH_and_elim_left hW1
  have hin1 := PrfH_and_elim_right hW1
  have hwf2 := PrfH_and_elim_left hW2
  have hargs2 := PrfH_and_elim_right hW2
  -- (1) LA FUSION: el testigo de la lista es `concat #1 #0`
  have hwfC := PrfH.mp _ _ _
    (prf_to_prfH (prf_wfAll1_concat (.var 1) (.var 0)) _) (PrfH_and_intro hwf1 hwf2)
  -- (2) la cabeza y la cola siguen cubiertas por el fusionado
  have hinC := PrfH.mp _ _ _ (prf_to_prfH (prf_In_mono_right_imp
    (liftTerm 0 (liftTerm 0 a)) (.var 0) (.var 1)) _) hin1
  have hargsC := PrfH.mp _ _ _ (prf_to_prfH (prf_argsIn_mono_of (.var 0)
    (concat (.var 1) (.var 0)) (liftTerm 0 (liftTerm 0 as))
    (fun x => prf_In_mono_imp x (liftTerm 0 (.var 0)) (liftTerm 0 (.var 1)))) _) hargs2
  have hargsCons := PrfH.mp _ _ _ (prf_to_prfH (prf_argsIn_cons_intro
    (concat (.var 1) (.var 0)) (liftTerm 0 (liftTerm 0 a))
    (liftTerm 0 (liftTerm 0 as))) _) (PrfH_and_intro hinC hargsC)
  refine PrfH_ex_intro (concat (.var 1) (.var 0)) ?_
  have hs : substFormula 0 (concat (.var 1) (.var 0))
      (land (wfAll1 (.var 0)) (argsIn (.var 0)
        (liftTerm 0 (cons (liftTerm 0 (liftTerm 0 a)) (liftTerm 0 (liftTerm 0 as))))))
      = land (wfAll1 (concat (.var 1) (.var 0)))
          (argsIn (concat (.var 1) (.var 0))
            (cons (liftTerm 0 (liftTerm 0 a)) (liftTerm 0 (liftTerm 0 as)))) := by
    simp only [land, substFormula, substF_wfAll1, substF_argsIn, substTerm, substTerms,
      if_true, FOL.substTerm_liftTerm]
  rw [hs]
  exact PrfH_and_intro hwfC hargsCons

/-! ## §12 · EL PASO, mitad LISTA — caso `cons`

`consOk X` parte la lista en `carc`/`cdrc`; `prf_argsIn_head`/`_tail` parten el `argsIn` del
contexto en las dos mitades correspondientes; Cantor baja a cada una, y §11 —la fusión— cierra. -/

private def HD : Term := carc (.var 3)
private def TL : Term := cdrc (.var 3)

private theorem caso_cons :
    PrfH (consOk (.var 3) :: CTX2) (hasWitArgs (substtsc (.var 1) (.var 0) (.var 3))) := by
  have hcons : PrfH (consOk (.var 3) :: CTX2) (consOk (.var 3)) := PrfH.hyp _ _ (List.Mem.head _)
  have hh : PrfH (consOk (.var 3) :: CTX2)
      (land (land (wfAll1 (.var 2)) (argsIn (.var 2) (.var 3))) (hasWit (.var 0))) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hpsi : PrfH (consOk (.var 3) :: CTX2)
      (liftFormula 0 (liftFormula 0 (liftFormula 0 (PSI PHIT)))) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  have hwf := PrfH_and_elim_left (PrfH_and_elim_left hh)
  have hargs0 := PrfH_and_elim_right (PrfH_and_elim_left hh)
  have hws := PrfH_and_elim_right hh
  -- (1) partir la lista y su `argsIn`
  have hargs : PrfH (consOk (.var 3) :: CTX2) (argsIn (.var 2) (cons HD TL)) :=
    PrfH_congr_argsIn hcons hargs0
  have hinHD := PrfH.mp _ _ _
    (prf_to_prfH (prf_argsIn_head (.var 2) HD TL) _) hargs
  have hargsTL := PrfH.mp _ _ _
    (prf_to_prfH (prf_argsIn_tail (.var 2) HD TL) _) hargs
  -- (2) Cantor: cabeza y cola son estrictamente menores que la lista
  have hcHD : Prf (lt HD (cons HD TL)) := prf_cantor_mono_left _ _
  have hcTL : Prf (lt TL (cons HD TL)) := prf_cantor_mono_right _ _
  have hltHD := ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2
    (PrfH_eq_symm hcons) (prf_to_prfH hcHD _)
  have hltTL := ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2
    (PrfH_eq_symm hcons) (prf_to_prfH hcTL _)
  -- (3) la HIPOTESIS DE INDUCCION en cada mitad
  have hihHD := PrfH.mp _ _ _ (PSI_inst3 PHIT hPHIT hpsi HD) hltHD
  have huseHD := PHIT_use HD (.var 2) (.var 1) (.var 0) hihHD
  have hHD := PrfH.mp _ _ _ (PrfH_and_elim_left huseHD)
    (PrfH_and_intro (PrfH_and_intro hwf hinHD) hws)
  have hihTL := PrfH.mp _ _ _ (PSI_inst3 PHIT hPHIT hpsi TL) hltTL
  have huseTL := PHIT_use TL (.var 2) (.var 1) (.var 0) hihTL
  have hTL := PrfH.mp _ _ _ (PrfH_and_elim_right huseTL)
    (PrfH_and_intro (PrfH_and_intro hwf hargsTL) hws)
  -- (4) LA FUSION (§11)
  have hfus := PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (prf_hasWitArgs_cons
    (substtc (.var 1) (.var 0) HD) (substtsc (.var 1) (.var 0) TL)) _) hHD) hTL
  -- (5) transporte al codigo original
  have h1 : PrfH (consOk (.var 3) :: CTX2)
      (substtsc (.var 1) (.var 0) (.var 3) =eq substtsc (.var 1) (.var 0) (cons HD TL)) :=
    PrfH_congr_substtsc3 hcons
  have h2 : PrfH (consOk (.var 3) :: CTX2)
      (substtsc (.var 1) (.var 0) (cons HD TL)
        =eq cons (substtc (.var 1) (.var 0) HD) (substtsc (.var 1) (.var 0) TL)) :=
    prf_to_prfH (prf_substtsc_cons (.var 1) (.var 0) HD TL) _
  exact PrfH_congr_hasWitArgs (PrfH_eq_symm (PrfH_eq_trans h1 h2)) hfus

/-! ## §13 · EL PASO, ENSAMBLADO — y el resultado de la mitad TÉRMINO -/

theorem PHIT_step : Prf (Formula.forall (Formula.impl (PSI PHIT) PHIT)) := by
  refine Prf.gen _ (prf_deduction ?_)
  refine PrfH.gen [PSI PHIT] _ ?_
  simp only [List.map_cons, List.map_nil]
  refine PrfH.gen _ _ ?_
  simp only [List.map_cons, List.map_nil]
  refine PrfH.gen _ _ ?_
  simp only [List.map_cons, List.map_nil]
  refine PrfH_and_intro ?half1 ?half2
  case half1 =>
    refine deduction_aux ?_ (land (isTC1 (.var 2) (.var 3)) (hasWit (.var 0)))
      [liftFormula 0 (liftFormula 0 (liftFormula 0 (PSI PHIT)))] rfl
    have hh : PrfH CTX1 (land (isTC1 (.var 2) (.var 3)) (hasWit (.var 0))) :=
      PrfH.hyp _ _ (List.Mem.head _)
    have hwf := PrfH_and_elim_left (PrfH_and_elim_left hh)
    have hin := PrfH_and_elim_right (PrfH_and_elim_left hh)
    have hnode := PrfH.mp _ _ _ (PrfH.mp _ _ _
      (prf_to_prfH (prf_isTermCodeE1_of_In (.var 2) (.var 3)) _) hin) hwf
    exact PrfH_or_elim hnode caso_varc caso_funcc
  case half2 =>
    refine deduction_aux ?_
      (land (land (wfAll1 (.var 2)) (argsIn (.var 2) (.var 3))) (hasWit (.var 0)))
      [liftFormula 0 (liftFormula 0 (liftFormula 0 (PSI PHIT)))] rfl
    exact PrfH_or_elim (prf_to_prfH (prf_nil_or_cons (.var 3)) _) caso_nil caso_cons

theorem PHIT_all (t : Term) : Prf (substFormula 0 t PHIT) :=
  prf_strong_induction PHIT hPHIT PHIT_step t

/-- **LA CLAUSURA, con testigo EXPLÍCITO** (la forma que sale de la inducción). -/
theorem prf_hasWit_substtc_of_isTC1 (w v s t : Term) :
    Prf (Formula.impl (land (isTC1 w t) (hasWit s)) (hasWit (substtc v s t))) :=
  prfH_nil_to_prf (PrfH_and_elim_left (PHIT_use t w v s (prf_to_prfH (PHIT_all t) []))) rfl

/-- 🏁 **LA CLAUSURA DEL SORTE TÉRMINO**: `hasWit` es cerrado bajo `substtc`.
    El testigo del código se elimina aquí; es la forma que consume la mitad de FÓRMULA. -/
theorem prf_hasWit_substtc (v s t : Term) :
    Prf (Formula.impl (hasWit t) (Formula.impl (hasWit s) (hasWit (substtc v s t)))) := by
  refine prf_ex_elim_imp ?_
  have hg : liftFormula 0 (Formula.impl (hasWit s) (hasWit (substtc v s t)))
      = Formula.impl (hasWit (liftTerm 0 s))
          (hasWit (substtc (liftTerm 0 v) (liftTerm 0 s) (liftTerm 0 t))) := by
    simp only [liftFormula, liftF_hasWit, substtc, liftTerm, liftTerms]
  rw [hg]
  refine deduction_aux ?_ (hasWit (liftTerm 0 s)) [isTC1 (.var 0) (liftTerm 0 t)] rfl
  have hitc : PrfH [hasWit (liftTerm 0 s), isTC1 (.var 0) (liftTerm 0 t)]
      (isTC1 (.var 0) (liftTerm 0 t)) := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hws : PrfH [hasWit (liftTerm 0 s), isTC1 (.var 0) (liftTerm 0 t)]
      (hasWit (liftTerm 0 s)) := PrfH.hyp _ _ (List.Mem.head _)
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_hasWit_substtc_of_isTC1 (.var 0)
    (liftTerm 0 v) (liftTerm 0 s) (liftTerm 0 t)) _) (PrfH_and_intro hitc hws)


/-! ## §15 · La mitad de LISTA, expuesta

La mitad 2 de la inducción, en forma consumible. Es lo que los casos `atom` (lista de argumentos)
de la mitad de FÓRMULA van a necesitar. -/

theorem prf_hasWitArgs_substtsc_of (w v s Y : Term) :
    Prf (Formula.impl (land (land (wfAll1 w) (argsIn w Y)) (hasWit s))
      (hasWitArgs (substtsc v s Y))) :=
  prfH_nil_to_prf (PrfH_and_elim_right (PHIT_use Y w v s (prf_to_prfH (PHIT_all Y) []))) rfl

/-! ## §16 · MITAD FÓRMULA — el armazón

`hasWitF` lleva DOS listas testigo (`wF` de fórmulas, `wT` de términos contra la que se valida),
así que `PHIT` tiene **cuatro** binders: `wF`(#3), `wT`(#2), `v`(#1), `s`(#0), y el código es `#4`.
Es la misma forma que `sondeos/EvalSubstfcPrf.lean:6302`, con otra conclusión.

A diferencia de la mitad TÉRMINO, aquí el cuerpo **no es conjuntivo**: la parte de lista ya está
resuelta arriba (§15) y entra como lema externo. -/

def BODYF (wF wT v s X : Term) : Formula :=
  Formula.impl (land (isFC1 wF wT X) (hasWit s)) (hasWitF (substfc v s X))

theorem liftF_BODYF (k : Nat) (wF wT v s X : Term) :
    liftFormula k (BODYF wF wT v s X)
      = BODYF (liftTerm k wF) (liftTerm k wT) (liftTerm k v) (liftTerm k s) (liftTerm k X) := by
  simp only [BODYF, land, liftFormula, liftF_isFC1, liftF_hasWit, liftF_hasWitF, substfc,
    liftTerm, liftTerms]

theorem substF_BODYF (k : Nat) (u wF wT v s X : Term) :
    substFormula k u (BODYF wF wT v s X)
      = BODYF (substTerm k u wF) (substTerm k u wT) (substTerm k u v) (substTerm k u s)
          (substTerm k u X) := by
  simp only [BODYF, land, substFormula, substF_isFC1, substF_hasWit, substF_hasWitF, substfc,
    substTerm, substTerms]

private def PHIFbody : Formula := BODYF (.var 3) (.var 2) (.var 1) (.var 0) (.var 4)

def PHIF : Formula :=
  Formula.forall (Formula.forall (Formula.forall (Formula.forall PHIFbody)))

/-- **EL GATE de la mitad FÓRMULA.** -/
theorem hPHIF : liftFormula 1 PHIF = PHIF := by
  simp only [PHIF, PHIFbody, liftFormula, liftF_BODYF, liftTerm, Nat.reduceAdd, Nat.reduceLT,
    reduceIte]

/-! ### Los cuatro colapsos de la mitad FÓRMULA -/

theorem PHIF_at (t : Term) :
    substFormula 0 t PHIF = Formula.forall (Formula.forall (Formula.forall (Formula.forall
      (BODYF (.var 3) (.var 2) (.var 1) (.var 0)
        (liftTerm 0 (liftTerm 0 (liftTerm 0 (liftTerm 0 t)))))))) := by
  simp only [PHIF, PHIFbody, substFormula, substF_BODYF, substTerm, Nat.reduceAdd,
    Nat.reduceEqDiff, Nat.reduceGT, Nat.reduceSub, reduceIte, if_true]

theorem PHIF_spec1 (t wF : Term) :
    substFormula 0 wF (Formula.forall (Formula.forall (Formula.forall
      (BODYF (.var 3) (.var 2) (.var 1) (.var 0)
        (liftTerm 0 (liftTerm 0 (liftTerm 0 (liftTerm 0 t))))))))
      = Formula.forall (Formula.forall (Formula.forall
          (BODYF (liftTerm 0 (liftTerm 0 (liftTerm 0 wF))) (.var 2) (.var 1) (.var 0)
            (liftTerm 0 (liftTerm 0 (liftTerm 0 t)))))) := by
  have h4 := substTerm_liftLiftLiftLift t 0 (liftTerm 0 (liftTerm 0 (liftTerm 0 wF)))
  simp only [substFormula, substF_BODYF, substTerm, Nat.reduceAdd, Nat.reduceEqDiff,
    Nat.reduceGT, Nat.reduceSub, reduceIte, if_true, FOL.substTerm_liftTerm, h4]

theorem PHIF_spec2 (t wF wT : Term) :
    substFormula 0 wT (Formula.forall (Formula.forall
      (BODYF (liftTerm 0 (liftTerm 0 (liftTerm 0 wF))) (.var 2) (.var 1) (.var 0)
        (liftTerm 0 (liftTerm 0 (liftTerm 0 t))))))
      = Formula.forall (Formula.forall
          (BODYF (liftTerm 0 (liftTerm 0 wF)) (liftTerm 0 (liftTerm 0 wT)) (.var 1) (.var 0)
            (liftTerm 0 (liftTerm 0 t)))) := by
  have h3 := substTerm_liftLiftLift t 0 (liftTerm 0 (liftTerm 0 wT))
  have hw := substTerm_liftLiftLift wF 0 (liftTerm 0 (liftTerm 0 wT))
  simp only [substFormula, substF_BODYF, substTerm, Nat.reduceAdd, Nat.reduceEqDiff,
    Nat.reduceGT, Nat.reduceSub, reduceIte, if_true, FOL.substTerm_liftTerm, h3, hw]

theorem PHIF_spec3 (t wF wT v : Term) :
    substFormula 0 v (Formula.forall
      (BODYF (liftTerm 0 (liftTerm 0 wF)) (liftTerm 0 (liftTerm 0 wT)) (.var 1) (.var 0)
        (liftTerm 0 (liftTerm 0 t))))
      = Formula.forall (BODYF (liftTerm 0 wF) (liftTerm 0 wT) (liftTerm 0 v) (.var 0)
          (liftTerm 0 t)) := by
  have h2 := FOL.substTerm_liftLift t 0 (liftTerm 0 v)
  have hF := FOL.substTerm_liftLift wF 0 (liftTerm 0 v)
  have hT := FOL.substTerm_liftLift wT 0 (liftTerm 0 v)
  simp only [substFormula, substF_BODYF, substTerm, Nat.reduceAdd, Nat.reduceEqDiff,
    Nat.reduceGT, Nat.reduceSub, reduceIte, if_true, FOL.substTerm_liftTerm, h2, hF, hT]

theorem PHIF_spec4 (t wF wT v s : Term) :
    substFormula 0 s (BODYF (liftTerm 0 wF) (liftTerm 0 wT) (liftTerm 0 v) (.var 0)
      (liftTerm 0 t)) = BODYF wF wT v s t := by
  simp only [substF_BODYF, substTerm, if_true, FOL.substTerm_liftTerm]

/-- Instanciación de los cuatro binders. -/
theorem PHIF_use {Γ : List Formula} (t wF wT v s : Term)
    (h : PrfH Γ (substFormula 0 t PHIF)) : PrfH Γ (BODYF wF wT v s t) := by
  rw [PHIF_at] at h
  have h1 := PrfH_spec h wF
  rw [PHIF_spec1] at h1
  have h2 := PrfH_spec h1 wT
  rw [PHIF_spec2] at h2
  have h3 := PrfH_spec h2 v
  rw [PHIF_spec3] at h3
  have h4 := PrfH_spec h3 s
  rwa [PHIF_spec4] at h4

/-! ## §17 · MONOTONÍA de `isFormCodeE2` — la pieza de la que cuelga la mitad FÓRMULA

`isFormCodeE2` es una disyunción de OCHO cláusulas, y el testigo entra en cada una sólo por `In`
o por `argsIn`. Así que cada cláusula es monótona por separado y se combinan con `or`-elim
encadenado. ⚠️ El testigo tiene **DOS** componentes: `wT` gobierna `clAtom`/`clEq` y `wF` gobierna
`clBin`/`clUn`; `clBot` no lleva testigo y es invariante. -/

/-- De `X ⇒ a` sale `X ⇒ a ∨ b`. -/
theorem prf_imp_orL {X a b : Formula} (h : Prf (Formula.impl X a)) :
    Prf (Formula.impl X (lor a b)) :=
  ROBINSON_PlusPlus.Meta.ReprPrf.prf_syll h (Prf.incl (Prf₀.j1 a b))

/-- De `X ⇒ b` sale `X ⇒ a ∨ b`. -/
theorem prf_imp_orR {X a b : Formula} (h : Prf (Formula.impl X b)) :
    Prf (Formula.impl X (lor a b)) :=
  ROBINSON_PlusPlus.Meta.ReprPrf.prf_syll h (Prf.incl (Prf₀.j2 a b))

/-- La identidad, como implicación. -/
theorem prf_imp_self (A : Formula) : Prf (Formula.impl A A) :=
  prf_deduction (prfH_hyp_self _)

/-- Conjunción monótona en la segunda componente. -/
theorem prf_and_mono_right {A B B' : Formula} (h : Prf (Formula.impl B B')) :
    Prf (Formula.impl (land A B) (land A B')) := by
  refine prf_deduction ?_
  have hh : PrfH [land A B] (land A B) := prfH_hyp_self _
  exact PrfH.mp _ _ _ (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.c1 _ _))
    (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.c2 _ _)) hh))
    (PrfH.mp _ _ _ (prf_to_prfH h _) (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.c3 _ _)) hh))

/-- `In x w ∧ In y w` es monótono. -/
theorem prf_inPair_mono_of (w w' x y : Term)
    (hsub : ∀ z : Term, Prf (Formula.impl (In z w) (In z w'))) :
    Prf (Formula.impl (land (In x w) (In y w)) (land (In x w') (In y w'))) := by
  refine prf_deduction ?_
  have hh : PrfH [land (In x w) (In y w)] (land (In x w) (In y w)) := prfH_hyp_self _
  exact PrfH.mp _ _ _ (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.c1 _ _))
    (PrfH.mp _ _ _ (prf_to_prfH (hsub x) _)
      (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.c2 _ _)) hh)))
    (PrfH.mp _ _ _ (prf_to_prfH (hsub y) _)
      (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.c3 _ _)) hh))

/-- **MONOTONÍA de `isFormCodeE2`** en los DOS testigos. -/
theorem prf_isFormCodeE2_mono_of (wF wF' wT wT' X : Term)
    (hF : ∀ z : Term, Prf (Formula.impl (In z wF) (In z wF')))
    (hTl : ∀ z : Term, Prf (Formula.impl (In z (liftTerm 0 wT)) (In z (liftTerm 0 wT'))))
    (hT : ∀ z : Term, Prf (Formula.impl (In z wT) (In z wT'))) :
    Prf (Formula.impl (isFormCodeE2 wF wT X) (isFormCodeE2 wF' wT' X)) := by
  unfold isFormCodeE2 lorAll
  refine prf_or_elim_imp (prf_imp_orL (prf_imp_self (clBot X))) ?_
  refine prf_or_elim_imp (prf_imp_orR (prf_imp_orL ?_)) ?_
  · -- clAtom: monotono en `wT` via `argsIn`
    exact prf_and_mono_right (prf_argsIn_mono_of wT wT' (nthc X (numeralM 2)) hTl)
  refine prf_or_elim_imp (prf_imp_orR (prf_imp_orR (prf_imp_orL ?_))) ?_
  · -- clEq: dos `In` contra `wT`
    exact prf_and_mono_right (prf_inPair_mono_of wT wT'
      (nthc X (numeralM 1)) (nthc X (numeralM 2)) hT)
  refine prf_or_elim_imp (prf_imp_orR (prf_imp_orR (prf_imp_orR (prf_imp_orL ?_)))) ?_
  · exact prf_and_mono_right (prf_inPair_mono_of wF wF'
      (nthc X (numeralM 1)) (nthc X (numeralM 2)) hF)
  refine prf_or_elim_imp (prf_imp_orR (prf_imp_orR (prf_imp_orR (prf_imp_orR
    (prf_imp_orL ?_))))) ?_
  · exact prf_and_mono_right (hF (nthc X (numeralM 1)))
  refine prf_or_elim_imp (prf_imp_orR (prf_imp_orR (prf_imp_orR (prf_imp_orR
    (prf_imp_orR (prf_imp_orL ?_)))))) ?_
  · exact prf_and_mono_right (prf_inPair_mono_of wF wF'
      (nthc X (numeralM 1)) (nthc X (numeralM 2)) hF)
  refine prf_or_elim_imp (prf_imp_orR (prf_imp_orR (prf_imp_orR (prf_imp_orR
    (prf_imp_orR (prf_imp_orR (prf_imp_orL ?_))))))) ?_
  · exact prf_and_mono_right (prf_inPair_mono_of wF wF'
      (nthc X (numeralM 1)) (nthc X (numeralM 2)) hF)
  · exact prf_imp_orR (prf_imp_orR (prf_imp_orR (prf_imp_orR (prf_imp_orR
      (prf_imp_orR (prf_imp_orR (prf_and_mono_right (hF (nthc X (numeralM 1)))))))))) 

/-! ## §18 · El testigo de FÓRMULAS: monotonía en `wT`, extensión y FUSIÓN

Mismo molde que §4 y §10 del sorte término. ⚠️ La asimetría: `wfAllF wF wT` **no** es monótono en
`wF` (que aparece también en la COTA `lenc wF`), pero sí en `wT`. Extender o fusionar `wF` va por
el corte de índice / la forma de pertenencia, igual que antes. -/

private def CTXf (A wF wT : Term) : List Formula :=
  [lt (.var 0) (lenc (cons (liftTerm 0 A) (liftTerm 0 wF))),
   land (isFormCodeE2 (cons (liftTerm 0 A) (liftTerm 0 wF)) (liftTerm 0 wT) (liftTerm 0 A))
     (wfAllF (liftTerm 0 wF) (liftTerm 0 wT))]

/-- **`wfAllF` es monótono en el testigo de TÉRMINOS.** -/
theorem prf_wfAllF_mono_wT (wF wT wT' : Term)
    (hT : ∀ z : Term, Prf (Formula.impl (In z (liftTerm 0 wT)) (In z (liftTerm 0 wT'))))
    (hTl : ∀ z : Term, Prf (Formula.impl (In z (liftTerm 0 (liftTerm 0 wT)))
      (In z (liftTerm 0 (liftTerm 0 wT'))))) :
    Prf (Formula.impl (wfAllF wF wT) (wfAllF wF wT')) := by
  refine prf_mp (Prf.qconf (wfAllF wF wT) (wfAllFBody wF wT')) (Prf.gen _ ?_)
  simp only [liftF_wfAllF]
  refine prf_deduction (deduction_aux ?_ (lt (.var 0) (liftTerm 0 (lenc wF)))
    [wfAllF (liftTerm 0 wF) (liftTerm 0 wT)] rfl)
  have hlt : PrfH [lt (.var 0) (lenc (liftTerm 0 wF)),
      wfAllF (liftTerm 0 wF) (liftTerm 0 wT)] (lt (.var 0) (lenc (liftTerm 0 wF))) :=
    PrfH.hyp _ _ (List.Mem.head _)
  have hw : PrfH [lt (.var 0) (lenc (liftTerm 0 wF)),
      wfAllF (liftTerm 0 wF) (liftTerm 0 wT)] (wfAllF (liftTerm 0 wF) (liftTerm 0 wT)) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hnode := PrfH.mp _ _ _
    (PrfH_inst_wfAllF (liftTerm 0 wF) (liftTerm 0 wT) (.var 0) hw) hlt
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_isFormCodeE2_mono_of
    (liftTerm 0 wF) (liftTerm 0 wF) (liftTerm 0 wT) (liftTerm 0 wT')
    (nthc (liftTerm 0 wF) (.var 0))
    (fun z => prf_imp_self (In z (liftTerm 0 wF))) hTl hT) _) hnode

/-- **EXTENSIÓN del testigo de FÓRMULAS con un nodo.** -/
theorem prf_wfAllF_cons (A wF wT : Term) :
    Prf (Formula.impl
      (land (isFormCodeE2 (cons A wF) wT A) (wfAllF wF wT)) (wfAllF (cons A wF) wT)) := by
  refine prf_mp (Prf.qconf (land (isFormCodeE2 (cons A wF) wT A) (wfAllF wF wT))
    (wfAllFBody (cons A wF) wT)) (Prf.gen _ ?_)
  simp only [liftFormula, liftF_isFormCodeE2, liftF_wfAllF, land]
  refine prf_deduction (deduction_aux ?_
    (lt (.var 0) (liftTerm 0 (lenc (cons A wF))))
    [land (isFormCodeE2 (cons (liftTerm 0 A) (liftTerm 0 wF)) (liftTerm 0 wT) (liftTerm 0 A))
      (wfAllF (liftTerm 0 wF) (liftTerm 0 wT))] rfl)
  refine PrfH_or_elim (prf_to_prfH (prf_zero_or_eq_succ_pred (.var 0)) _) ?zc ?sc
  case zc =>
    have hz : PrfH (Formula.eq (.var 0) zero :: CTXf A wF wT) (Formula.eq (.var 0) zero) :=
      PrfH.hyp _ _ (List.Mem.head _)
    have hA : PrfH (Formula.eq (.var 0) zero :: CTXf A wF wT)
        (isFormCodeE2 (cons (liftTerm 0 A) (liftTerm 0 wF)) (liftTerm 0 wT) (liftTerm 0 A)) :=
      PrfH_and_elim_left (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
    have hnth : PrfH (Formula.eq (.var 0) zero :: CTXf A wF wT)
        (nthc (cons (liftTerm 0 A) (liftTerm 0 wF)) (.var 0) =eq liftTerm 0 A) :=
      PrfH_eq_trans (PrfH_congr_nthc_idx _ hz)
        (prf_to_prfH (prf_nthc_zero (liftTerm 0 A) (liftTerm 0 wF)) _)
    exact PrfH_congr_isFormCodeE2 (PrfH_eq_symm hnth) hA
  case sc =>
    have hs : PrfH (Formula.eq (.var 0) (succ (pred (.var 0))) :: CTXf A wF wT)
        (Formula.eq (.var 0) (succ (pred (.var 0)))) := PrfH.hyp _ _ (List.Mem.head _)
    have hlt2 : PrfH (Formula.eq (.var 0) (succ (pred (.var 0))) :: CTXf A wF wT)
        (lt (.var 0) (lenc (cons (liftTerm 0 A) (liftTerm 0 wF)))) :=
      PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
    have hw : PrfH (Formula.eq (.var 0) (succ (pred (.var 0))) :: CTXf A wF wT)
        (wfAllF (liftTerm 0 wF) (liftTerm 0 wT)) :=
      PrfH_and_elim_right (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
    have hltS : PrfH (Formula.eq (.var 0) (succ (pred (.var 0))) :: CTXf A wF wT)
        (lt (succ (pred (.var 0))) (succ (lenc (liftTerm 0 wF)))) :=
      ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2
        (prf_to_prfH (prf_lenc_cons (liftTerm 0 A) (liftTerm 0 wF)) _)
        (ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst1 hs hlt2)
    have hltw : PrfH (Formula.eq (.var 0) (succ (pred (.var 0))) :: CTXf A wF wT)
        (lt (pred (.var 0)) (lenc (liftTerm 0 wF))) :=
      PrfH.mp _ _ _ (prf_to_prfH
        (prf_lt_of_succ_lt_succ (pred (.var 0)) (lenc (liftTerm 0 wF))) _) hltS
    have hnode := PrfH.mp _ _ _
      (PrfH_inst_wfAllF (liftTerm 0 wF) (liftTerm 0 wT) (pred (.var 0)) hw) hltw
    have hmono := PrfH.mp _ _ _ (prf_to_prfH (prf_isFormCodeE2_mono_of
      (liftTerm 0 wF) (cons (liftTerm 0 A) (liftTerm 0 wF))
      (liftTerm 0 wT) (liftTerm 0 wT) (nthc (liftTerm 0 wF) (pred (.var 0)))
      (fun z => prf_in_cons_tail_imp (liftTerm 0 A) z (liftTerm 0 wF))
      (fun z => prf_imp_self (In z (liftTerm 0 (liftTerm 0 wT))))
      (fun z => prf_imp_self (In z (liftTerm 0 wT)))) _) hnode
    have hnth : PrfH (Formula.eq (.var 0) (succ (pred (.var 0))) :: CTXf A wF wT)
        (nthc (cons (liftTerm 0 A) (liftTerm 0 wF)) (.var 0)
          =eq nthc (liftTerm 0 wF) (pred (.var 0))) :=
      PrfH_eq_trans (PrfH_congr_nthc_idx _ hs)
        (prf_to_prfH (prf_nthc_succ (liftTerm 0 A) (liftTerm 0 wF) (pred (.var 0))) _)
    exact PrfH_congr_isFormCodeE2 (PrfH_eq_symm hnth) hmono

/-! ## §19 · LA FUSIÓN del testigo de FÓRMULAS

Misma ruta que §10 (TAREA A): forma de PERTENENCIA —donde `concat` es axioma—, `or`-elim sobre
las dos mitades, y vuelta por monotonía. `prf_isFormCodeE2_of_In` ya existía. -/

private def CTXfc (WF1 WF2 wT : Term) : List Formula :=
  [lt (.var 0) (lenc (concat (liftTerm 0 WF1) (liftTerm 0 WF2))),
   land (wfAllF (liftTerm 0 WF1) (liftTerm 0 wT)) (wfAllF (liftTerm 0 WF2) (liftTerm 0 wT))]

theorem prf_wfAllF_concat (WF1 WF2 wT : Term) :
    Prf (Formula.impl (land (wfAllF WF1 wT) (wfAllF WF2 wT))
      (wfAllF (concat WF1 WF2) wT)) := by
  refine prf_mp (Prf.qconf (land (wfAllF WF1 wT) (wfAllF WF2 wT))
    (wfAllFBody (concat WF1 WF2) wT)) (Prf.gen _ ?_)
  simp only [liftFormula, liftF_wfAllF, land]
  refine prf_deduction (deduction_aux ?_
    (lt (.var 0) (liftTerm 0 (lenc (concat WF1 WF2))))
    [land (wfAllF (liftTerm 0 WF1) (liftTerm 0 wT))
      (wfAllF (liftTerm 0 WF2) (liftTerm 0 wT))] rfl)
  have hlt : PrfH (CTXfc WF1 WF2 wT)
      (lt (.var 0) (lenc (concat (liftTerm 0 WF1) (liftTerm 0 WF2)))) :=
    PrfH.hyp _ _ (List.Mem.head _)
  have hinC : PrfH (CTXfc WF1 WF2 wT)
      (In (nthc (concat (liftTerm 0 WF1) (liftTerm 0 WF2)) (.var 0))
        (concat (liftTerm 0 WF1) (liftTerm 0 WF2))) :=
    PrfH.mp _ _ _ (prf_to_prfH
      (prf_in_nthc (concat (liftTerm 0 WF1) (liftTerm 0 WF2)) (.var 0)) _) hlt
  have hor : PrfH (CTXfc WF1 WF2 wT)
      (lor (In (nthc (concat (liftTerm 0 WF1) (liftTerm 0 WF2)) (.var 0)) (liftTerm 0 WF1))
           (In (nthc (concat (liftTerm 0 WF1) (liftTerm 0 WF2)) (.var 0)) (liftTerm 0 WF2))) :=
    PrfH.mp _ _ _ (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.c2 _ _))
      (prf_to_prfH (prf_in_concat
        (nthc (concat (liftTerm 0 WF1) (liftTerm 0 WF2)) (.var 0))
        (liftTerm 0 WF1) (liftTerm 0 WF2)) _)) hinC
  refine PrfH_or_elim hor ?iz ?dr
  case iz =>
    have hin : PrfH (In (nthc (concat (liftTerm 0 WF1) (liftTerm 0 WF2)) (.var 0))
          (liftTerm 0 WF1) :: CTXfc WF1 WF2 wT)
        (In (nthc (concat (liftTerm 0 WF1) (liftTerm 0 WF2)) (.var 0)) (liftTerm 0 WF1)) :=
      PrfH.hyp _ _ (List.Mem.head _)
    have hw : PrfH (In (nthc (concat (liftTerm 0 WF1) (liftTerm 0 WF2)) (.var 0))
          (liftTerm 0 WF1) :: CTXfc WF1 WF2 wT)
        (wfAllF (liftTerm 0 WF1) (liftTerm 0 wT)) :=
      PrfH_and_elim_left (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
    have hnode := PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH
      (prf_isFormCodeE2_of_In (liftTerm 0 WF1) (liftTerm 0 wT)
        (nthc (concat (liftTerm 0 WF1) (liftTerm 0 WF2)) (.var 0))) _) hin) hw
    exact PrfH.mp _ _ _ (prf_to_prfH (prf_isFormCodeE2_mono_of
      (liftTerm 0 WF1) (concat (liftTerm 0 WF1) (liftTerm 0 WF2))
      (liftTerm 0 wT) (liftTerm 0 wT)
      (nthc (concat (liftTerm 0 WF1) (liftTerm 0 WF2)) (.var 0))
      (fun z => prf_In_mono_right_imp z (liftTerm 0 WF2) (liftTerm 0 WF1))
      (fun z => prf_imp_self (In z (liftTerm 0 (liftTerm 0 wT))))
      (fun z => prf_imp_self (In z (liftTerm 0 wT)))) _) hnode
  case dr =>
    have hin : PrfH (In (nthc (concat (liftTerm 0 WF1) (liftTerm 0 WF2)) (.var 0))
          (liftTerm 0 WF2) :: CTXfc WF1 WF2 wT)
        (In (nthc (concat (liftTerm 0 WF1) (liftTerm 0 WF2)) (.var 0)) (liftTerm 0 WF2)) :=
      PrfH.hyp _ _ (List.Mem.head _)
    have hw : PrfH (In (nthc (concat (liftTerm 0 WF1) (liftTerm 0 WF2)) (.var 0))
          (liftTerm 0 WF2) :: CTXfc WF1 WF2 wT)
        (wfAllF (liftTerm 0 WF2) (liftTerm 0 wT)) :=
      PrfH_and_elim_right (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
    have hnode := PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH
      (prf_isFormCodeE2_of_In (liftTerm 0 WF2) (liftTerm 0 wT)
        (nthc (concat (liftTerm 0 WF1) (liftTerm 0 WF2)) (.var 0))) _) hin) hw
    exact PrfH.mp _ _ _ (prf_to_prfH (prf_isFormCodeE2_mono_of
      (liftTerm 0 WF2) (concat (liftTerm 0 WF1) (liftTerm 0 WF2))
      (liftTerm 0 wT) (liftTerm 0 wT)
      (nthc (concat (liftTerm 0 WF1) (liftTerm 0 WF2)) (.var 0))
      (fun z => prf_In_mono_imp z (liftTerm 0 WF2) (liftTerm 0 WF1))
      (fun z => prf_imp_self (In z (liftTerm 0 (liftTerm 0 wT))))
      (fun z => prf_imp_self (In z (liftTerm 0 wT)))) _) hnode

/-! ## §20 · Los NODOS de fórmula, genéricos en el tag

`implc`/`andc`/`orc` son el mismo nodo binario con tag 5/7/8, y `forallc`/`exc` el mismo unario
con 6/9 — definicionalmente. Se prueba UNA vez cada forma y se instancia. -/

/-- Nodo BINARIO de tag `k`: `⟨k̄, a, b⟩`. -/
def binN (k : Nat) (a b : Term) : Term := cons (numeralM k) (cons a (cons b nil))
/-- Nodo UNARIO de tag `k`: `⟨k̄, a⟩`. -/
def unN (k : Nat) (a : Term) : Term := cons (numeralM k) (cons a nil)

theorem prf_nthc_binN1 (k : Nat) (a b : Term) :
    Prf (nthc (binN k a b) (numeralM 1) =eq a) := prf_nthc_c1 (numeralM k) a (cons b nil)
theorem prf_nthc_binN2 (k : Nat) (a b : Term) :
    Prf (nthc (binN k a b) (numeralM 2) =eq b) := prf_nthc_c2 (numeralM k) a b nil
theorem prf_nthc_unN1 (k : Nat) (a : Term) :
    Prf (nthc (unN k a) (numeralM 1) =eq a) := prf_nthc_c1 (numeralM k) a nil

theorem prf_shapeBin_binN (k : Nat) (a b : Term) : Prf (shapeBin (binN k a b) k) :=
  prf_eq_symm (prf_congr_cons_tail (prf_eq_trans
    (prf_congr_cons_head (prf_nthc_binN1 k a b))
    (prf_congr_cons_tail (prf_congr_cons_head (prf_nthc_binN2 k a b)))))

theorem prf_shapeUn_unN (k : Nat) (a : Term) : Prf (shapeUn (unN k a) k) :=
  prf_eq_symm (prf_congr_cons_tail (prf_congr_cons_head (prf_nthc_unN1 k a)))

/-- La cláusula BINARIA del nodo, con sus dos casillas en el testigo. -/
theorem prf_clBin_node (wF a b : Term) (k : Nat)
    (ha : Prf (In a wF)) (hb : Prf (In b wF)) : Prf (clBin wF (binN k a b) k) :=
  prf_and_intro (prf_shapeBin_binN k a b)
    (prf_and_intro
      (prf_congr_In_left (prf_eq_symm (prf_nthc_binN1 k a b)) ha)
      (prf_congr_In_left (prf_eq_symm (prf_nthc_binN2 k a b)) hb))

/-- La cláusula UNARIA del nodo. -/
theorem prf_clUn_node (wF a : Term) (k : Nat) (ha : Prf (In a wF)) :
    Prf (clUn wF (unN k a) k) :=
  prf_and_intro (prf_shapeUn_unN k a)
    (prf_congr_In_left (prf_eq_symm (prf_nthc_unN1 k a)) ha)

/-- Las mismas, en forma de IMPLICACIÓN: es como llegan cuando la pertenencia viene del
    contexto `PrfH` y no como `Prf` (la moneda OBJETO otra vez). -/
theorem prf_clUn_node_imp (wF a : Term) (k : Nat) :
    Prf (Formula.impl (In a wF) (clUn wF (unN k a) k)) := by
  refine prf_deduction ?_
  have h : PrfH [In a wF] (In a wF) := prfH_hyp_self _
  exact PrfH.mp _ _ _ (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.c1 _ _))
    (prf_to_prfH (prf_shapeUn_unN k a) _))
    (PrfH_congr_In_left (prf_to_prfH (prf_eq_symm (prf_nthc_unN1 k a)) _) h)

theorem prf_clBin_node_imp (wF a b : Term) (k : Nat) :
    Prf (Formula.impl (land (In a wF) (In b wF)) (clBin wF (binN k a b) k)) := by
  refine prf_deduction ?_
  have h : PrfH [land (In a wF) (In b wF)] (land (In a wF) (In b wF)) := prfH_hyp_self _
  have ha := PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.c2 _ _)) h
  have hb := PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.c3 _ _)) h
  exact PrfH.mp _ _ _ (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.c1 _ _))
    (prf_to_prfH (prf_shapeBin_binN k a b) _))
    (PrfH.mp _ _ _ (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.c1 _ _))
      (PrfH_congr_In_left (prf_to_prfH (prf_eq_symm (prf_nthc_binN1 k a b)) _) ha))
      (PrfH_congr_In_left (prf_to_prfH (prf_eq_symm (prf_nthc_binN2 k a b)) _) hb))

/-! ## §21 · Las OCHO inyecciones en `isFormCodeE2`

`isFormCodeE2` es `clBot ∨ (clAtom ∨ (clEq ∨ (clBin 5 ∨ (clUn 6 ∨ (clBin 7 ∨ (clBin 8 ∨ clUn 9))))))`.
Cada caso entra por su posición. -/

theorem inj_bot (wF wT X : Term) : Prf (Formula.impl (clBot X) (isFormCodeE2 wF wT X)) :=
  prf_imp_orL (prf_imp_self _)
theorem inj_atom (wF wT X : Term) : Prf (Formula.impl (clAtom wT X) (isFormCodeE2 wF wT X)) :=
  prf_imp_orR (prf_imp_orL (prf_imp_self _))
theorem inj_eq (wF wT X : Term) : Prf (Formula.impl (clEq wT X) (isFormCodeE2 wF wT X)) :=
  prf_imp_orR (prf_imp_orR (prf_imp_orL (prf_imp_self _)))
theorem inj_bin5 (wF wT X : Term) : Prf (Formula.impl (clBin wF X 5) (isFormCodeE2 wF wT X)) :=
  prf_imp_orR (prf_imp_orR (prf_imp_orR (prf_imp_orL (prf_imp_self _))))
theorem inj_un6 (wF wT X : Term) : Prf (Formula.impl (clUn wF X 6) (isFormCodeE2 wF wT X)) :=
  prf_imp_orR (prf_imp_orR (prf_imp_orR (prf_imp_orR (prf_imp_orL (prf_imp_self _)))))
theorem inj_bin7 (wF wT X : Term) : Prf (Formula.impl (clBin wF X 7) (isFormCodeE2 wF wT X)) :=
  prf_imp_orR (prf_imp_orR (prf_imp_orR (prf_imp_orR (prf_imp_orR (prf_imp_orL
    (prf_imp_self _))))))
theorem inj_bin8 (wF wT X : Term) : Prf (Formula.impl (clBin wF X 8) (isFormCodeE2 wF wT X)) :=
  prf_imp_orR (prf_imp_orR (prf_imp_orR (prf_imp_orR (prf_imp_orR (prf_imp_orR
    (prf_imp_orL (prf_imp_self _)))))))
theorem inj_un9 (wF wT X : Term) : Prf (Formula.impl (clUn wF X 9) (isFormCodeE2 wF wT X)) :=
  prf_imp_orR (prf_imp_orR (prf_imp_orR (prf_imp_orR (prf_imp_orR (prf_imp_orR
    (prf_imp_orR (prf_imp_self _)))))))

/-! ## §22 · INTRODUCIR el testigo, y los DOS constructores con testigos ABSTRACTOS

🔑 **La regla de método otra vez** (§3.37.4): *sacar el `∃` fuera del paso*. Toda la fusión se hace
aquí con los testigos **abstractos** —ni un índice De Bruijn que mover— y en forma de
**IMPLICACIÓN objeto**, que es como llegan las cosas desde un contexto `PrfH`. Los existenciales se
eliminan en §23, y allí cada caso es un solo `mp`. -/

/-- **Introducción de la guarda existencial**: dos `q2` encadenados. Es `prf_hasWitF_real` en
    abstracto, y en forma de implicación OBJETO. -/
theorem prf_hasWitF_imp (wF wT X : Term) :
    Prf (Formula.impl (isFC1 wF wT X) (hasWitF X)) := by
  have h2 : Prf (Formula.impl
      (substFormula 0 wT (isFC1 (liftTerm 0 wF) (.var 0) (liftTerm 0 X)))
      (Formula.ex (isFC1 (liftTerm 0 wF) (.var 0) (liftTerm 0 X)))) :=
    Prf.incl (Prf₀.q2 _ wT)
  have h2' : Prf (Formula.impl (isFC1 wF wT X)
      (Formula.ex (isFC1 (liftTerm 0 wF) (.var 0) (liftTerm 0 X)))) := by
    simpa only [substF_isFC1, substTerm, if_true, FOL.substTerm_liftTerm] using h2
  have h1 : Prf (Formula.impl (substFormula 0 wF (Formula.ex (isFC1 (.var 1) (.var 0)
      (liftTerm 0 (liftTerm 0 X))))) (hasWitF X)) := Prf.incl (Prf₀.q2 _ wF)
  have hz1 : (0 = 1) = False := eq_false (by omega)
  have h1' : Prf (Formula.impl (Formula.ex (isFC1 (liftTerm 0 wF) (.var 0) (liftTerm 0 X)))
      (hasWitF X)) := by
    simpa only [substFormula, substF_isFC1, substTerm, Nat.reduceAdd, Nat.reduceLT,
      Nat.reduceGT, Nat.reduceSub, reduceIte, if_true, hz1, if_false,
      FOL.substTerm_liftLift] using h1
  exact ROBINSON_PlusPlus.Meta.ReprPrf.prf_syll h2' h1'

/-- **El nodo UNARIO con testigo abstracto**: basta EXTENDER el testigo de fórmulas con el nodo;
    el de términos no se toca. -/
theorem prf_isFC1_unN (k : Nat) (A wF wT : Term)
    (inj : ∀ wF wT X : Term, Prf (Formula.impl (clUn wF X k) (isFormCodeE2 wF wT X))) :
    Prf (Formula.impl (isFC1 wF wT A)
      (isFC1 (cons (unN k A) wF) wT (unN k A))) := by
  refine prf_deduction ?_
  have h : PrfH [isFC1 wF wT A] (isFC1 wF wT A) := prfH_hyp_self _
  have hwT := PrfH_and_elim_left (PrfH_and_elim_left h)
  have hwF := PrfH_and_elim_right (PrfH_and_elim_left h)
  have hin := PrfH_and_elim_right h
  have hinC := PrfH.mp _ _ _ (prf_to_prfH (prf_in_cons_tail_imp (unN k A) A wF) _) hin
  have hcl := PrfH.mp _ _ _ (prf_to_prfH (prf_clUn_node_imp (cons (unN k A) wF) A k) _) hinC
  have hnode := PrfH.mp _ _ _ (prf_to_prfH (inj (cons (unN k A) wF) wT (unN k A)) _) hcl
  have hwF' := PrfH.mp _ _ _ (prf_to_prfH (prf_wfAllF_cons (unN k A) wF wT) _)
    (PrfH_and_intro hnode hwF)
  exact PrfH_and_intro (PrfH_and_intro hwT hwF')
    (prf_to_prfH (prf_in_cons_head (unN k A) wF) _)

/-- **El nodo BINARIO con testigos abstractos** — LA FUSIÓN de los dos componentes: `concat` en el
    testigo de términos (TAREA A) y en el de fórmulas (§19), monotonía para que cada mitad siga
    cubriendo lo suyo, y extensión con el nodo. -/
theorem prf_isFC1_binN (k : Nat) (A B wFa wTa wFb wTb : Term)
    (inj : ∀ wF wT X : Term, Prf (Formula.impl (clBin wF X k) (isFormCodeE2 wF wT X))) :
    Prf (Formula.impl (land (isFC1 wFa wTa A) (isFC1 wFb wTb B))
      (isFC1 (cons (binN k A B) (concat wFa wFb)) (concat wTa wTb) (binN k A B))) := by
  refine prf_deduction ?_
  have h : PrfH [land (isFC1 wFa wTa A) (isFC1 wFb wTb B)]
      (land (isFC1 wFa wTa A) (isFC1 wFb wTb B)) := prfH_hyp_self _
  have ha := PrfH_and_elim_left h
  have hb := PrfH_and_elim_right h
  have hwTa := PrfH_and_elim_left (PrfH_and_elim_left ha)
  have hwFa := PrfH_and_elim_right (PrfH_and_elim_left ha)
  have hina := PrfH_and_elim_right ha
  have hwTb := PrfH_and_elim_left (PrfH_and_elim_left hb)
  have hwFb := PrfH_and_elim_right (PrfH_and_elim_left hb)
  have hinb := PrfH_and_elim_right hb
  -- (1) el testigo de TERMINOS se fusiona (TAREA A)
  have hwT := PrfH.mp _ _ _ (prf_to_prfH (prf_wfAll1_concat wTa wTb) _)
    (PrfH_and_intro hwTa hwTb)
  -- (2) los dos `wfAllF` suben al `wT` fusionado, y luego se fusionan entre si (§18-§19)
  have hwFa2 := PrfH.mp _ _ _ (prf_to_prfH (prf_wfAllF_mono_wT wFa wTa (concat wTa wTb)
    (fun z => prf_In_mono_right_imp z (liftTerm 0 wTb) (liftTerm 0 wTa))
    (fun z => prf_In_mono_right_imp z (liftTerm 0 (liftTerm 0 wTb))
      (liftTerm 0 (liftTerm 0 wTa)))) _) hwFa
  have hwFb2 := PrfH.mp _ _ _ (prf_to_prfH (prf_wfAllF_mono_wT wFb wTb (concat wTa wTb)
    (fun z => prf_In_mono_imp z (liftTerm 0 wTb) (liftTerm 0 wTa))
    (fun z => prf_In_mono_imp z (liftTerm 0 (liftTerm 0 wTb))
      (liftTerm 0 (liftTerm 0 wTa)))) _) hwFb
  have hwFc := PrfH.mp _ _ _ (prf_to_prfH (prf_wfAllF_concat wFa wFb (concat wTa wTb)) _)
    (PrfH_and_intro hwFa2 hwFb2)
  -- (3) las dos casillas siguen en el testigo EXTENDIDO
  have hinaC := PrfH.mp _ _ _
    (prf_to_prfH (prf_in_cons_tail_imp (binN k A B) A (concat wFa wFb)) _)
    (PrfH.mp _ _ _ (prf_to_prfH (prf_In_mono_right_imp A wFb wFa) _) hina)
  have hinbC := PrfH.mp _ _ _
    (prf_to_prfH (prf_in_cons_tail_imp (binN k A B) B (concat wFa wFb)) _)
    (PrfH.mp _ _ _ (prf_to_prfH (prf_In_mono_imp B wFb wFa) _) hinb)
  -- (4) el nodo, y la extension del testigo de formulas
  have hcl := PrfH.mp _ _ _
    (prf_to_prfH (prf_clBin_node_imp (cons (binN k A B) (concat wFa wFb)) A B k) _)
    (PrfH_and_intro hinaC hinbC)
  have hnode := PrfH.mp _ _ _
    (prf_to_prfH (inj (cons (binN k A B) (concat wFa wFb)) (concat wTa wTb) (binN k A B)) _) hcl
  have hwF' := PrfH.mp _ _ _
    (prf_to_prfH (prf_wfAllF_cons (binN k A B) (concat wFa wFb) (concat wTa wTb)) _)
    (PrfH_and_intro hnode hwFc)
  exact PrfH_and_intro (PrfH_and_intro hwT hwF')
    (prf_to_prfH (prf_in_cons_head (binN k A B) (concat wFa wFb)) _)

/-! ## §23 · Los dos constructores, ya SIN testigos

Se eliminan los existenciales (dos por operando) y se aplica §22. Es donde se ve el ahorro: el
cuerpo de cada uno son cuatro líneas, porque toda la fusión ya está pagada en abstracto. -/

/-- El contexto que dejan las DOS eliminaciones del caso unario. -/
private def CTXu (a : Term) : List Formula :=
  [isFC1 (.var 1) (.var 0) (liftTerm 0 (liftTerm 0 a)),
   liftFormula 0 (Formula.ex (isFC1 (.var 1) (.var 0) (liftTerm 0 (liftTerm 0 a))))]

theorem prf_hasWitF_un (k : Nat) (a : Term)
    (inj : ∀ wF wT X : Term, Prf (Formula.impl (clUn wF X k) (isFormCodeE2 wF wT X))) :
    Prf (Formula.impl (hasWitF a) (hasWitF (unN k a))) := by
  refine prf_ex_elim_imp ?_
  refine PrfH_ex_elim (PrfH.hyp _ _ (List.Mem.head _)) ?_
  simp only [List.map_cons, List.map_nil]
  have hF : PrfH (CTXu a) (isFC1 (.var 1) (.var 0) (liftTerm 0 (liftTerm 0 a))) :=
    PrfH.hyp _ _ (List.Mem.head _)
  have hg : liftFormula 0 (liftFormula 0 (hasWitF (unN k a)))
      = hasWitF (unN k (liftTerm 0 (liftTerm 0 a))) := by
    simp only [liftF_hasWitF, unN, cons, nil, zero, liftTerm, liftTerms, liftTerm_numeralM]
  rw [hg]
  have hstep := PrfH.mp _ _ _ (prf_to_prfH
    (prf_isFC1_unN k (liftTerm 0 (liftTerm 0 a)) (.var 1) (.var 0) inj) _) hF
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_hasWitF_imp
    (cons (unN k (liftTerm 0 (liftTerm 0 a))) (.var 1)) (.var 0)
    (unN k (liftTerm 0 (liftTerm 0 a)))) _) hstep

/-- El contexto que dejan las CUATRO eliminaciones del caso binario: los testigos de `a` quedan en
    `#3`/`#2` y los de `b` en `#1`/`#0`, y los códigos con CUATRO lifts. -/
private def CTXb (a b : Term) : List Formula :=
  [isFC1 (.var 1) (.var 0) (liftTerm 0 (liftTerm 0 (liftTerm 0 (liftTerm 0 b)))),
   liftFormula 0 (Formula.ex (isFC1 (.var 1) (.var 0)
     (liftTerm 0 (liftTerm 0 (liftTerm 0 (liftTerm 0 b)))))),
   liftFormula 0 (liftFormula 0 (hasWitF (liftTerm 0 (liftTerm 0 b)))),
   liftFormula 0 (liftFormula 0 (isFC1 (.var 1) (.var 0) (liftTerm 0 (liftTerm 0 a)))),
   liftFormula 0 (liftFormula 0 (liftFormula 0 (Formula.ex (isFC1 (.var 1) (.var 0)
     (liftTerm 0 (liftTerm 0 a))))))]

theorem prf_hasWitF_bin (k : Nat) (a b : Term)
    (inj : ∀ wF wT X : Term, Prf (Formula.impl (clBin wF X k) (isFormCodeE2 wF wT X))) :
    Prf (Formula.impl (hasWitF a) (Formula.impl (hasWitF b) (hasWitF (binN k a b)))) := by
  refine prf_ex_elim_imp ?_
  refine PrfH_ex_elim (PrfH.hyp _ _ (List.Mem.head _)) ?_
  simp only [List.map_cons, List.map_nil]
  have hgb : liftFormula 0 (liftFormula 0 (Formula.impl (hasWitF b) (hasWitF (binN k a b))))
      = Formula.impl (hasWitF (liftTerm 0 (liftTerm 0 b)))
          (hasWitF (binN k (liftTerm 0 (liftTerm 0 a)) (liftTerm 0 (liftTerm 0 b)))) := by
    simp only [liftFormula, liftF_hasWitF, binN, cons, nil, zero, liftTerm, liftTerms,
      liftTerm_numeralM]
  rw [hgb]
  refine deduction_aux ?_ (hasWitF (liftTerm 0 (liftTerm 0 b)))
    [isFC1 (.var 1) (.var 0) (liftTerm 0 (liftTerm 0 a)),
     liftFormula 0 (Formula.ex (isFC1 (.var 1) (.var 0) (liftTerm 0 (liftTerm 0 a))))] rfl
  refine PrfH_ex_elim (PrfH.hyp _ _ (List.Mem.head _)) ?_
  simp only [List.map_cons, List.map_nil]
  refine PrfH_ex_elim (PrfH.hyp _ _ (List.Mem.head _)) ?_
  simp only [List.map_cons, List.map_nil]
  -- testigos de `b`: `#1`/`#0`, directos;  de `a`: `#3`/`#2`, tras los dos lifts de contexto
  have hFb : PrfH (CTXb a b) (isFC1 (.var 1) (.var 0)
      (liftTerm 0 (liftTerm 0 (liftTerm 0 (liftTerm 0 b))))) := PrfH.hyp _ _ (List.Mem.head _)
  have hFa : PrfH (CTXb a b) (liftFormula 0 (liftFormula 0
      (isFC1 (.var 1) (.var 0) (liftTerm 0 (liftTerm 0 a))))) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
  have hFa' : PrfH (CTXb a b) (isFC1 (.var 3) (.var 2)
      (liftTerm 0 (liftTerm 0 (liftTerm 0 (liftTerm 0 a))))) := by
    simpa only [liftF_isFC1, liftTerm, Nat.reduceAdd, Nat.reduceLT, reduceIte] using hFa
  have hgoal : liftFormula 0 (liftFormula 0 (hasWitF (binN k (liftTerm 0 (liftTerm 0 a))
      (liftTerm 0 (liftTerm 0 b)))))
      = hasWitF (binN k (liftTerm 0 (liftTerm 0 (liftTerm 0 (liftTerm 0 a))))
          (liftTerm 0 (liftTerm 0 (liftTerm 0 (liftTerm 0 b))))) := by
    simp only [liftF_hasWitF, binN, cons, nil, zero, liftTerm, liftTerms, liftTerm_numeralM]
  rw [hgoal]
  have hstep := PrfH.mp _ _ _ (prf_to_prfH (prf_isFC1_binN k
    (liftTerm 0 (liftTerm 0 (liftTerm 0 (liftTerm 0 a))))
    (liftTerm 0 (liftTerm 0 (liftTerm 0 (liftTerm 0 b))))
    (.var 3) (.var 2) (.var 1) (.var 0) inj) _) (PrfH_and_intro hFa' hFb)
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_hasWitF_imp
    (cons (binN k (liftTerm 0 (liftTerm 0 (liftTerm 0 (liftTerm 0 a))))
      (liftTerm 0 (liftTerm 0 (liftTerm 0 (liftTerm 0 b))))) (concat (.var 3) (.var 1)))
    (concat (.var 2) (.var 0))
    (binN k (liftTerm 0 (liftTerm 0 (liftTerm 0 (liftTerm 0 a))))
      (liftTerm 0 (liftTerm 0 (liftTerm 0 (liftTerm 0 b)))))) _) hstep

/-! ## §24 · Las piezas que el PASO de fórmula consume y no existían

Cuatro grupos: (a) el testigo de fórmulas VACÍO y las congruencias que faltaban; (b) el cuarto
escalón de la escalera `psi` —`PHIF` tiene CUATRO binders y `PSI_inst3` sólo llega a tres—;
(c) los tres constructores SIN inducción (`botc`, `atomc`, `eqc`), que se cierran con la mitad
TÉRMINO y no necesitan la HI.

⚠️ `PrfH_congr_substfc3` vive en `Meta/BdAllIntroPrf.lean`, que importa `MpCodePrf` y está en
ROJO: **tercera** pieza que el árbol parado obliga a reproducir. -/

/-- El testigo de FÓRMULAS vacío es bien formado (vacuamente). -/
theorem prf_wfAllF_nil (wT : Term) : Prf (wfAllF nil wT) := by
  refine Prf.gen _ (prf_deduction ?_)
  have hlt : PrfH [lt (.var 0) (liftTerm 0 (lenc nil))] (lt (.var 0) (lenc nil)) :=
    prfH_hyp_self _
  have hz : PrfH [lt (.var 0) (liftTerm 0 (lenc nil))] (lt (.var 0) zero) :=
    ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2 (prf_to_prfH prf_lenc_nil _) hlt
  exact PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.efq _))
    (PrfH.mp _ _ _ (prf_to_prfH (prf_not_lt_zero (.var 0)) _) hz)

/-- Congruencia de `hasWitF` en `PrfH` (espejo de `PrfH_congr_hasWit`). -/
theorem PrfH_congr_hasWitF {Γ : List Formula} {a b : Term}
    (h : PrfH Γ (a =eq b)) (hw : PrfH Γ (hasWitF a)) : PrfH Γ (hasWitF b) := by
  have e : ∀ x : Term, substFormula 0 x (hasWitF (.var 0)) = hasWitF x := by
    intro x; simp only [substF_hasWitF, substTerm, if_true]
  exact (e b) ▸ ROBINSON_PlusPlus.Meta.ChainPrf.PrfH_leibniz_subst
    (A := hasWitF (.var 0)) h ((e a) ▸ hw)

/-! ### Los TRES constructores que no necesitan la hipótesis de inducción

`botc` no tiene subfórmulas; `atomc` y `eqc` tienen argumentos de sorte **TÉRMINO**, y para ésos
la clausura ya está probada arriba (§13, §15). Por eso la mitad FÓRMULA no es conjuntiva. -/

/-- `⊥` codificado tiene testigo: `⟨[botc], []⟩`. -/
theorem prf_hasWitF_bot : Prf (hasWitF botc) := by
  have hnode : Prf (isFormCodeE2 (cons botc nil) nil botc) :=
    prf_mp (inj_bot (cons botc nil) nil botc) (prf_refl botc)
  have hwF : Prf (wfAllF (cons botc nil) nil) :=
    prf_mp (prf_wfAllF_cons botc nil nil) (prf_and_intro hnode (prf_wfAllF_nil nil))
  exact prf_mp (prf_hasWitF_imp (cons botc nil) nil botc)
    (prf_and_intro (prf_and_intro prf_wfAll1_nil hwF) (prf_in_cons_head botc nil))

/-- **Un átomo cuyos argumentos comparten testigo, tiene testigo de fórmula.**
    El testigo de términos es el de la lista; el de fórmulas es el nodo solo. -/
theorem prf_hasWitF_atomc (P Y : Term) :
    Prf (Formula.impl (hasWitArgs Y) (hasWitF (atomc P Y))) := by
  refine prf_ex_elim_imp ?_
  have hgoal : liftFormula 0 (hasWitF (atomc P Y))
      = hasWitF (atomc (liftTerm 0 P) (liftTerm 0 Y)) := by
    simp only [liftF_hasWitF, atomc, cons, nil, zero, succ, liftTerm, liftTerms]
  rw [hgoal]
  have hctx : PrfH [land (wfAll1 (.var 0)) (argsIn (.var 0) (liftTerm 0 Y))]
      (land (wfAll1 (.var 0)) (argsIn (.var 0) (liftTerm 0 Y))) := prfH_hyp_self _
  have hwf := PrfH_and_elim_left hctx
  have hargs := PrfH_and_elim_right hctx
  have hcl : PrfH [land (wfAll1 (.var 0)) (argsIn (.var 0) (liftTerm 0 Y))]
      (clAtom (.var 0) (atomc (liftTerm 0 P) (liftTerm 0 Y))) :=
    PrfH_and_intro (prf_to_prfH (prf_shapeBin_binN 3 (liftTerm 0 P) (liftTerm 0 Y)) _)
      (PrfH_congr_argsIn (prf_to_prfH (prf_eq_symm
        (prf_nthc_binN2 3 (liftTerm 0 P) (liftTerm 0 Y))) _) hargs)
  have hnode := PrfH.mp _ _ _ (prf_to_prfH (inj_atom
    (cons (atomc (liftTerm 0 P) (liftTerm 0 Y)) nil) (.var 0)
    (atomc (liftTerm 0 P) (liftTerm 0 Y))) _) hcl
  have hwF := PrfH.mp _ _ _ (prf_to_prfH (prf_wfAllF_cons
    (atomc (liftTerm 0 P) (liftTerm 0 Y)) nil (.var 0)) _)
    (PrfH_and_intro hnode (prf_to_prfH (prf_wfAllF_nil (.var 0)) _))
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_hasWitF_imp
    (cons (atomc (liftTerm 0 P) (liftTerm 0 Y)) nil) (.var 0)
    (atomc (liftTerm 0 P) (liftTerm 0 Y))) _)
    (PrfH_and_intro (PrfH_and_intro hwf hwF)
      (prf_to_prfH (prf_in_cons_head (atomc (liftTerm 0 P) (liftTerm 0 Y)) nil) _))

/-- El contexto que dejan las DOS eliminaciones del caso `eqc`. -/
private def CTXe (a b : Term) : List Formula :=
  [isTC1 (.var 0) (liftTerm 0 (liftTerm 0 b)),
   liftFormula 0 (hasWit (liftTerm 0 b)),
   liftFormula 0 (isTC1 (.var 0) (liftTerm 0 a))]

/-- **Una ecuación con los dos lados con testigo, tiene testigo de fórmula.**
    Aquí se fusionan DOS testigos de TÉRMINO (`prf_wfAll1_concat`, TAREA A). -/
theorem prf_hasWitF_eqc (a b : Term) :
    Prf (Formula.impl (hasWit a) (Formula.impl (hasWit b) (hasWitF (eqc a b)))) := by
  refine prf_ex_elim_imp ?_
  have hg1 : liftFormula 0 (Formula.impl (hasWit b) (hasWitF (eqc a b)))
      = Formula.impl (hasWit (liftTerm 0 b))
          (hasWitF (eqc (liftTerm 0 a) (liftTerm 0 b))) := by
    simp only [liftFormula, liftF_hasWit, liftF_hasWitF, eqc, cons, nil, zero, succ,
      liftTerm, liftTerms]
  rw [hg1]
  refine deduction_aux ?_ (hasWit (liftTerm 0 b)) [isTC1 (.var 0) (liftTerm 0 a)] rfl
  refine PrfH_ex_elim (PrfH.hyp _ _ (List.Mem.head _)) ?_
  simp only [List.map_cons, List.map_nil]
  have hgoal : liftFormula 0 (hasWitF (eqc (liftTerm 0 a) (liftTerm 0 b)))
      = hasWitF (eqc (liftTerm 0 (liftTerm 0 a)) (liftTerm 0 (liftTerm 0 b))) := by
    simp only [liftF_hasWitF, eqc, cons, nil, zero, succ, liftTerm, liftTerms]
  rw [hgoal]
  have hb : PrfH (CTXe a b) (isTC1 (.var 0) (liftTerm 0 (liftTerm 0 b))) :=
    PrfH.hyp _ _ (List.Mem.head _)
  have ha0 : PrfH (CTXe a b) (liftFormula 0 (isTC1 (.var 0) (liftTerm 0 a))) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  have ha : PrfH (CTXe a b) (isTC1 (.var 1) (liftTerm 0 (liftTerm 0 a))) := by
    simpa only [liftF_isTC1, liftTerm, Nat.reduceAdd, Nat.reduceLT, reduceIte] using ha0
  have hwT := PrfH.mp _ _ _ (prf_to_prfH (prf_wfAll1_concat (.var 1) (.var 0)) _)
    (PrfH_and_intro (PrfH_and_elim_left ha) (PrfH_and_elim_left hb))
  have hinA := PrfH.mp _ _ _ (prf_to_prfH (prf_In_mono_right_imp
    (liftTerm 0 (liftTerm 0 a)) (.var 0) (.var 1)) _) (PrfH_and_elim_right ha)
  have hinB := PrfH.mp _ _ _ (prf_to_prfH (prf_In_mono_imp
    (liftTerm 0 (liftTerm 0 b)) (.var 0) (.var 1)) _) (PrfH_and_elim_right hb)
  have hcl : PrfH (CTXe a b) (clEq (concat (.var 1) (.var 0))
      (eqc (liftTerm 0 (liftTerm 0 a)) (liftTerm 0 (liftTerm 0 b)))) :=
    PrfH_and_intro (prf_to_prfH (prf_shapeBin_binN 4
        (liftTerm 0 (liftTerm 0 a)) (liftTerm 0 (liftTerm 0 b))) _)
      (PrfH_and_intro
        (PrfH_congr_In_left (prf_to_prfH (prf_eq_symm (prf_nthc_binN1 4
          (liftTerm 0 (liftTerm 0 a)) (liftTerm 0 (liftTerm 0 b)))) _) hinA)
        (PrfH_congr_In_left (prf_to_prfH (prf_eq_symm (prf_nthc_binN2 4
          (liftTerm 0 (liftTerm 0 a)) (liftTerm 0 (liftTerm 0 b)))) _) hinB))
  have hnode := PrfH.mp _ _ _ (prf_to_prfH (inj_eq
    (cons (eqc (liftTerm 0 (liftTerm 0 a)) (liftTerm 0 (liftTerm 0 b))) nil)
    (concat (.var 1) (.var 0))
    (eqc (liftTerm 0 (liftTerm 0 a)) (liftTerm 0 (liftTerm 0 b)))) _) hcl
  have hwF := PrfH.mp _ _ _ (prf_to_prfH (prf_wfAllF_cons
    (eqc (liftTerm 0 (liftTerm 0 a)) (liftTerm 0 (liftTerm 0 b))) nil
    (concat (.var 1) (.var 0))) _)
    (PrfH_and_intro hnode (prf_to_prfH (prf_wfAllF_nil (concat (.var 1) (.var 0))) _))
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_hasWitF_imp
    (cons (eqc (liftTerm 0 (liftTerm 0 a)) (liftTerm 0 (liftTerm 0 b))) nil)
    (concat (.var 1) (.var 0))
    (eqc (liftTerm 0 (liftTerm 0 a)) (liftTerm 0 (liftTerm 0 b)))) _)
    (PrfH_and_intro (PrfH_and_intro hwT hwF)
      (prf_to_prfH (prf_in_cons_head
        (eqc (liftTerm 0 (liftTerm 0 a)) (liftTerm 0 (liftTerm 0 b))) nil) _))

/-! ## §25 · EL PASO de la mitad FÓRMULA — los OCHO casos

🔑 **Cada caso es GENÉRICO en el contexto y recibe por argumento exactamente las hipótesis que
usa** (la cláusula, la guarda, y —los cinco que inducen— la HI de curso de valores). Es lo que
evita la contabilidad de los siete `or`-elim anidados: un caso a profundidad `d` vive en un
contexto con `d` disyunciones residuales delante, y escribir ese contexto ocho veces era el
grueso del trabajo. Así sólo cambian los índices del `List.Mem` en el ensamblaje.

Reparto: `bot` es inmediato; `atom` y `eq` **consumen la mitad TÉRMINO** (§13/§15) y no inducen;
los tres `bin` (5/7/8) y los dos `un` (6/9) usan la HI, con la escalera de Cantor para bajar. -/

/-- Los dos operandos del nodo, cuando el código resulta ser binario (o el único, si es unario). -/
private def AF : Term := nthc (.var 4) (numeralM 1)
private def BF : Term := nthc (.var 4) (numeralM 2)

/-- **Caso `botc`**: `⊥` no tiene subfórmulas y `substfc` lo deja igual. -/
private theorem casoF_bot {Γ : List Formula} (hcl : PrfH Γ (clBot (.var 4))) :
    PrfH Γ (hasWitF (substfc (.var 1) (.var 0) (.var 4))) := by
  have heq : PrfH Γ (substfc (.var 1) (.var 0) (.var 4) =eq botc) :=
    PrfH_eq_trans (PrfH_congr_substfc3 hcl)
      (prf_to_prfH (prf_substfc_bottom (.var 1) (.var 0)) _)
  exact PrfH_congr_hasWitF (PrfH_eq_symm heq) (prf_to_prfH prf_hasWitF_bot _)

/-- **Caso `atomc`**: la casilla 2 es una LISTA de códigos de término; la cierra §15. -/
private theorem casoF_atom {Γ : List Formula} (hcl : PrfH Γ (clAtom (.var 2) (.var 4)))
    (hg : PrfH Γ (land (isFC1 (.var 3) (.var 2) (.var 4)) (hasWit (.var 0)))) :
    PrfH Γ (hasWitF (substfc (.var 1) (.var 0) (.var 4))) := by
  have hshape := PrfH_and_elim_left hcl
  have hargs := PrfH_and_elim_right hcl
  have hwT := PrfH_and_elim_left (PrfH_and_elim_left (PrfH_and_elim_left hg))
  have hws := PrfH_and_elim_right hg
  have hargsW := PrfH.mp _ _ _ (prf_to_prfH (prf_hasWitArgs_substtsc_of
    (.var 2) (.var 1) (.var 0) BF) _)
    (PrfH_and_intro (PrfH_and_intro hwT hargs) hws)
  have hnode := PrfH.mp _ _ _ (prf_to_prfH
    (prf_hasWitF_atomc AF (substtsc (.var 1) (.var 0) BF)) _) hargsW
  have h1 : PrfH Γ (substfc (.var 1) (.var 0) (.var 4)
      =eq substfc (.var 1) (.var 0) (atomc AF BF)) := PrfH_congr_substfc3 hshape
  have h2 : PrfH Γ (substfc (.var 1) (.var 0) (atomc AF BF)
      =eq atomc AF (substtsc (.var 1) (.var 0) BF)) :=
    prf_to_prfH (prf_substfc_atom (.var 1) (.var 0) AF BF) _
  exact PrfH_congr_hasWitF (PrfH_eq_symm (PrfH_eq_trans h1 h2)) hnode

/-- **Caso `eqc`**: las DOS casillas son códigos de término; las cierra §13, y los dos testigos
    se fusionan en `prf_hasWitF_eqc`. -/
private theorem casoF_eq {Γ : List Formula} (hcl : PrfH Γ (clEq (.var 2) (.var 4)))
    (hg : PrfH Γ (land (isFC1 (.var 3) (.var 2) (.var 4)) (hasWit (.var 0)))) :
    PrfH Γ (hasWitF (substfc (.var 1) (.var 0) (.var 4))) := by
  have hshape := PrfH_and_elim_left hcl
  have hins := PrfH_and_elim_right hcl
  have hinA := PrfH_and_elim_left hins
  have hinB := PrfH_and_elim_right hins
  have hwT := PrfH_and_elim_left (PrfH_and_elim_left (PrfH_and_elim_left hg))
  have hws := PrfH_and_elim_right hg
  have hA := PrfH.mp _ _ _ (prf_to_prfH (prf_hasWit_substtc_of_isTC1
    (.var 2) (.var 1) (.var 0) AF) _) (PrfH_and_intro (PrfH_and_intro hwT hinA) hws)
  have hB := PrfH.mp _ _ _ (prf_to_prfH (prf_hasWit_substtc_of_isTC1
    (.var 2) (.var 1) (.var 0) BF) _) (PrfH_and_intro (PrfH_and_intro hwT hinB) hws)
  have hnode := PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (prf_hasWitF_eqc
    (substtc (.var 1) (.var 0) AF) (substtc (.var 1) (.var 0) BF)) _) hA) hB
  have h1 : PrfH Γ (substfc (.var 1) (.var 0) (.var 4)
      =eq substfc (.var 1) (.var 0) (eqc AF BF)) := PrfH_congr_substfc3 hshape
  have h2 : PrfH Γ (substfc (.var 1) (.var 0) (eqc AF BF)
      =eq eqc (substtc (.var 1) (.var 0) AF) (substtc (.var 1) (.var 0) BF)) :=
    prf_to_prfH (prf_substfc_eq (.var 1) (.var 0) AF BF) _
  exact PrfH_congr_hasWitF (PrfH_eq_symm (PrfH_eq_trans h1 h2)) hnode

/-- **Los tres casos BINARIOS** (`implc`/`andc`/`orc`, tags 5/7/8), de una vez: sólo cambian el
    tag, la inyección y la ecuación de `substfc`. Dos descensos de Cantor y la fusión de §23. -/
private theorem casoF_bin {Γ : List Formula} (k : Nat)
    (inj : ∀ wF wT X : Term, Prf (Formula.impl (clBin wF X k) (isFormCodeE2 wF wT X)))
    (heqn : ∀ v s a b : Term, Prf (substfc v s (binN k a b)
      =eq binN k (substfc v s a) (substfc v s b)))
    (hcl : PrfH Γ (clBin (.var 3) (.var 4) k))
    (hg : PrfH Γ (land (isFC1 (.var 3) (.var 2) (.var 4)) (hasWit (.var 0))))
    (hpsi : PrfH Γ (liftFormula 0 (liftFormula 0 (liftFormula 0
      (liftFormula 0 (PSI PHIF)))))) :
    PrfH Γ (hasWitF (substfc (.var 1) (.var 0) (.var 4))) := by
  have hshape := PrfH_and_elim_left hcl
  have hins := PrfH_and_elim_right hcl
  have hinA := PrfH_and_elim_left hins
  have hinB := PrfH_and_elim_right hins
  have hwT := PrfH_and_elim_left (PrfH_and_elim_left (PrfH_and_elim_left hg))
  have hwF := PrfH_and_elim_right (PrfH_and_elim_left (PrfH_and_elim_left hg))
  have hws := PrfH_and_elim_right hg
  -- LA CADENA DE CANTOR: los dos operandos son estrictamente menores que el nodo
  have cA1 : Prf (lt AF (cons AF (cons BF nil))) := prf_cantor_mono_left _ _
  have cA2 : Prf (lt (cons AF (cons BF nil)) (binN k AF BF)) := prf_cantor_mono_right _ _
  have cA : Prf (lt AF (binN k AF BF)) := prf_mp (prf_mp (prf_lt_trans _ _ _) cA1) cA2
  have cB1 : Prf (lt BF (cons BF nil)) := prf_cantor_mono_left _ _
  have cB2 : Prf (lt (cons BF nil) (cons AF (cons BF nil))) := prf_cantor_mono_right _ _
  have cB12 : Prf (lt BF (cons AF (cons BF nil))) :=
    prf_mp (prf_mp (prf_lt_trans _ _ _) cB1) cB2
  have cB : Prf (lt BF (binN k AF BF)) := prf_mp (prf_mp (prf_lt_trans _ _ _) cB12) cA2
  have hltA := ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2
    (PrfH_eq_symm hshape) (prf_to_prfH cA _)
  have hltB := ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2
    (PrfH_eq_symm hshape) (prf_to_prfH cB _)
  -- LA HIPOTESIS DE INDUCCION, una por operando (cuarto escalon de la escalera psi)
  have hihA := PrfH.mp _ _ _ (PSI_inst4 PHIF hPHIF hpsi AF) hltA
  have hA := PrfH.mp _ _ _ (PHIF_use AF (.var 3) (.var 2) (.var 1) (.var 0) hihA)
    (PrfH_and_intro (PrfH_and_intro (PrfH_and_intro hwT hwF) hinA) hws)
  have hihB := PrfH.mp _ _ _ (PSI_inst4 PHIF hPHIF hpsi BF) hltB
  have hB := PrfH.mp _ _ _ (PHIF_use BF (.var 3) (.var 2) (.var 1) (.var 0) hihB)
    (PrfH_and_intro (PrfH_and_intro (PrfH_and_intro hwT hwF) hinB) hws)
  have hnode := PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (prf_hasWitF_bin k
    (substfc (.var 1) (.var 0) AF) (substfc (.var 1) (.var 0) BF) inj) _) hA) hB
  have h1 : PrfH Γ (substfc (.var 1) (.var 0) (.var 4)
      =eq substfc (.var 1) (.var 0) (binN k AF BF)) := PrfH_congr_substfc3 hshape
  have h2 : PrfH Γ (substfc (.var 1) (.var 0) (binN k AF BF)
      =eq binN k (substfc (.var 1) (.var 0) AF) (substfc (.var 1) (.var 0) BF)) :=
    prf_to_prfH (heqn (.var 1) (.var 0) AF BF) _
  exact PrfH_congr_hasWitF (PrfH_eq_symm (PrfH_eq_trans h1 h2)) hnode

/-- **Los dos casos UNARIOS** (`forallc`/`exc`, tags 6/9). El binder SUBE el nivel: la HI se aplica
    con `v+1` y con el sustituyendo LEVANTADO, y por eso hace falta `CRIT_hasWit_lift`. -/
private theorem casoF_un {Γ : List Formula} (k : Nat)
    (inj : ∀ wF wT X : Term, Prf (Formula.impl (clUn wF X k) (isFormCodeE2 wF wT X)))
    (heqn : ∀ v s a : Term, Prf (substfc v s (unN k a)
      =eq unN k (substfc (succ v) (liftc zero s) a)))
    (hcl : PrfH Γ (clUn (.var 3) (.var 4) k))
    (hg : PrfH Γ (land (isFC1 (.var 3) (.var 2) (.var 4)) (hasWit (.var 0))))
    (hpsi : PrfH Γ (liftFormula 0 (liftFormula 0 (liftFormula 0
      (liftFormula 0 (PSI PHIF)))))) :
    PrfH Γ (hasWitF (substfc (.var 1) (.var 0) (.var 4))) := by
  have hshape := PrfH_and_elim_left hcl
  have hinA := PrfH_and_elim_right hcl
  have hwT := PrfH_and_elim_left (PrfH_and_elim_left (PrfH_and_elim_left hg))
  have hwF := PrfH_and_elim_right (PrfH_and_elim_left (PrfH_and_elim_left hg))
  have hws := PrfH_and_elim_right hg
  have cA1 : Prf (lt AF (cons AF nil)) := prf_cantor_mono_left _ _
  have cA2 : Prf (lt (cons AF nil) (unN k AF)) := prf_cantor_mono_right _ _
  have cA : Prf (lt AF (unN k AF)) := prf_mp (prf_mp (prf_lt_trans _ _ _) cA1) cA2
  have hltA := ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2
    (PrfH_eq_symm hshape) (prf_to_prfH cA _)
  have hihA := PrfH.mp _ _ _ (PSI_inst4 PHIF hPHIF hpsi AF) hltA
  -- el sustituyendo sube de nivel: su testigo lo da `CRIT_hasWit_lift`
  have hwsL := PrfH.mp _ _ _ (prf_to_prfH (CRIT_hasWit_lift (.var 0)) _) hws
  have hA := PrfH.mp _ _ _
    (PHIF_use AF (.var 3) (.var 2) (succ (.var 1)) (liftc zero (.var 0)) hihA)
    (PrfH_and_intro (PrfH_and_intro (PrfH_and_intro hwT hwF) hinA) hwsL)
  have hnode := PrfH.mp _ _ _ (prf_to_prfH (prf_hasWitF_un k
    (substfc (succ (.var 1)) (liftc zero (.var 0)) AF) inj) _) hA
  have h1 : PrfH Γ (substfc (.var 1) (.var 0) (.var 4)
      =eq substfc (.var 1) (.var 0) (unN k AF)) := PrfH_congr_substfc3 hshape
  have h2 : PrfH Γ (substfc (.var 1) (.var 0) (unN k AF)
      =eq unN k (substfc (succ (.var 1)) (liftc zero (.var 0)) AF)) :=
    prf_to_prfH (heqn (.var 1) (.var 0) AF) _
  exact PrfH_congr_hasWitF (PrfH_eq_symm (PrfH_eq_trans h1 h2)) hnode

/-! ## §26 · EL PASO ENSAMBLADO, y 🏁 LA CLAUSURA DE FÓRMULA

Siete `or`-elim anidados sobre las ocho cláusulas de `isFormCodeE2`. En cada rama la guarda está
a profundidad `d+1` y la HI a `d+2`: es toda la contabilidad que queda. -/

/-- Contexto de la mitad FÓRMULA tras introducir su antecedente. -/
private def CTXF : List Formula :=
  [land (isFC1 (.var 3) (.var 2) (.var 4)) (hasWit (.var 0)),
   liftFormula 0 (liftFormula 0 (liftFormula 0 (liftFormula 0 (PSI PHIF))))]

theorem PHIF_step : Prf (Formula.forall (Formula.impl (PSI PHIF) PHIF)) := by
  refine Prf.gen _ (prf_deduction ?_)
  refine PrfH.gen [PSI PHIF] _ ?_
  simp only [List.map_cons, List.map_nil]
  refine PrfH.gen _ _ ?_
  simp only [List.map_cons, List.map_nil]
  refine PrfH.gen _ _ ?_
  simp only [List.map_cons, List.map_nil]
  refine PrfH.gen _ _ ?_
  simp only [List.map_cons, List.map_nil]
  refine deduction_aux ?_ (land (isFC1 (.var 3) (.var 2) (.var 4)) (hasWit (.var 0)))
    [liftFormula 0 (liftFormula 0 (liftFormula 0 (liftFormula 0 (PSI PHIF))))] rfl
  have hg : PrfH CTXF (land (isFC1 (.var 3) (.var 2) (.var 4)) (hasWit (.var 0))) :=
    PrfH.hyp _ _ (List.Mem.head _)
  have hcode := PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH
      (prf_isFormCodeE2_of_In (.var 3) (.var 2) (.var 4)) _)
      (PrfH_and_elim_right (PrfH_and_elim_left hg)))
    (PrfH_and_elim_right (PrfH_and_elim_left (PrfH_and_elim_left hg)))
  -- 1 · botc
  refine PrfH_or_elim hcode (casoF_bot (PrfH.hyp _ _ (List.Mem.head _))) ?_
  -- 2 · atomc
  refine PrfH_or_elim (PrfH.hyp _ _ (List.Mem.head _))
    (casoF_atom (PrfH.hyp _ _ (List.Mem.head _))
      (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))) ?_
  -- 3 · eqc
  refine PrfH_or_elim (PrfH.hyp _ _ (List.Mem.head _))
    (casoF_eq (PrfH.hyp _ _ (List.Mem.head _))
      (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.head _)))))) ?_
  -- 4 · implc (tag 5)
  refine PrfH_or_elim (PrfH.hyp _ _ (List.Mem.head _))
    (casoF_bin 5 inj_bin5 (fun v s a b => prf_substfc_impl v s a b)
      (PrfH.hyp _ _ (List.Mem.head _))
      (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.head _))))))
      (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))) ?_
  -- 5 · forallc (tag 6)
  refine PrfH_or_elim (PrfH.hyp _ _ (List.Mem.head _))
    (casoF_un 6 inj_un6 (fun v s a => prf_substfc_forall v s a)
      (PrfH.hyp _ _ (List.Mem.head _))
      (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
      (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))) ?_
  -- 6 · andc (tag 7)
  refine PrfH_or_elim (PrfH.hyp _ _ (List.Mem.head _))
    (casoF_bin 7 inj_bin7 (fun v s a b => prf_substfc_and v s a b)
      (PrfH.hyp _ _ (List.Mem.head _))
      (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
      (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
          (List.Mem.tail _ (List.Mem.head _)))))))))) ?_
  -- 7 · orc (tag 8) y 8 · exc (tag 9)
  refine PrfH_or_elim (PrfH.hyp _ _ (List.Mem.head _))
    (casoF_bin 8 inj_bin8 (fun v s a b => prf_substfc_or v s a b)
      (PrfH.hyp _ _ (List.Mem.head _))
      (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
          (List.Mem.tail _ (List.Mem.head _)))))))))
      (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
          (List.Mem.tail _ (List.Mem.head _))))))))))) ?_
  exact casoF_un 9 inj_un9 (fun v s a => prf_substfc_ex v s a)
    (PrfH.hyp _ _ (List.Mem.head _))
    (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.head _)))))))))
    (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.head _))))))))))

theorem PHIF_all (t : Term) : Prf (substFormula 0 t PHIF) :=
  prf_strong_induction PHIF hPHIF PHIF_step t

/-- **LA CLAUSURA DE FÓRMULA, con testigo EXPLÍCITO.** -/
theorem prf_hasWitF_substfc_of_isFC1 (wF wT v s X : Term) :
    Prf (Formula.impl (land (isFC1 wF wT X) (hasWit s)) (hasWitF (substfc v s X))) :=
  prfH_nil_to_prf (PHIF_use X wF wT v s (prf_to_prfH (PHIF_all X) [])) rfl

/-- El contexto que dejan las dos eliminaciones de `hasWitF X`. -/
private def CTXs (s X : Term) : List Formula :=
  [hasWit (liftTerm 0 (liftTerm 0 s)),
   isFC1 (.var 1) (.var 0) (liftTerm 0 (liftTerm 0 X)),
   liftFormula 0 (Formula.ex (isFC1 (.var 1) (.var 0) (liftTerm 0 (liftTerm 0 X))))]

/-- 🏁 **LA PIEZA QUE FALTABA PARA EL VERDE** (§3.36.5): `hasWitF` es cerrado bajo `substfc`,
    con el código y el sustituyendo ABSTRACTOS. Es lo que piden los 6 sitios duros de
    `Meta/MpCodePrf.lean` bajo la enmienda ADR-020. -/
theorem prf_hasWitF_substfc (v s X : Term) :
    Prf (Formula.impl (hasWitF X) (Formula.impl (hasWit s) (hasWitF (substfc v s X)))) := by
  refine prf_ex_elim_imp ?_
  refine PrfH_ex_elim (PrfH.hyp _ _ (List.Mem.head _)) ?_
  simp only [List.map_cons, List.map_nil]
  have hg : liftFormula 0 (liftFormula 0
      (Formula.impl (hasWit s) (hasWitF (substfc v s X))))
      = Formula.impl (hasWit (liftTerm 0 (liftTerm 0 s)))
          (hasWitF (substfc (liftTerm 0 (liftTerm 0 v)) (liftTerm 0 (liftTerm 0 s))
            (liftTerm 0 (liftTerm 0 X)))) := by
    simp only [liftFormula, liftF_hasWit, liftF_hasWitF, substfc, liftTerm, liftTerms]
  rw [hg]
  refine deduction_aux ?_ (hasWit (liftTerm 0 (liftTerm 0 s)))
    [isFC1 (.var 1) (.var 0) (liftTerm 0 (liftTerm 0 X)),
     liftFormula 0 (Formula.ex (isFC1 (.var 1) (.var 0)
       (liftTerm 0 (liftTerm 0 X))))] rfl
  have hF : PrfH (CTXs s X) (isFC1 (.var 1) (.var 0) (liftTerm 0 (liftTerm 0 X))) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hws : PrfH (CTXs s X) (hasWit (liftTerm 0 (liftTerm 0 s))) :=
    PrfH.hyp _ _ (List.Mem.head _)
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_hasWitF_substfc_of_isFC1 (.var 1) (.var 0)
    (liftTerm 0 (liftTerm 0 v)) (liftTerm 0 (liftTerm 0 s))
    (liftTerm 0 (liftTerm 0 X))) _) (PrfH_and_intro hF hws)

/-- La forma de APLICACIÓN, que es como la piden los 6 sitios duros de `MpCodePrf`. -/
theorem prf_hasWitF_substfc_mp (v s X : Term)
    (hX : Prf (hasWitF X)) (hs : Prf (hasWit s)) : Prf (hasWitF (substfc v s X)) :=
  prf_mp (prf_mp (prf_hasWitF_substfc v s X) hX) hs

/-! ## §28 · LA ESCALERA DE ARIDAD — el kit que paga los constructores DOTADOS

⭐ **Es la pieza que hace mecánica la propagación** (③ de §3.39.3). El árbol tiene ~35
constructores de la **imagen punteada** —`addcT`, `succcT`, `carcT`, `cdrcT`, `nthcT`, `mulcT`,
`consT`, `div2cT`, `lencT`, `predcT`, `liftcT`, `substfcT`, `nulT`/`unT`/`binT`, `cpOfT`,
`eqCodeFn`, `atom1CodeFn`/`atom2CodeFn`, `ltCodeFn`…— y bajo ADR-020 cada sitio que los pasa como
testigo o como código tiene que pagar su guarda.

🔑 **Pero NO hacen falta ~35 lemas, hacen falta SEIS.** Medido: todos los de sorte TÉRMINO son
`funcc (strCode σ) ⟨x₁,…,xₙ⟩` con n ≤ 3, y todos los de sorte FÓRMULA son nodos `eqc`/`atomc`.
Así que basta una escalera por aridad, y cada constructor concreto se paga después **en una
línea**, aguas abajo, donde esté definido.

⚠️ **Y una trampa registrada que aquí NO muerde, comprobado con `rfl`**: `eqCodeFn` usa
`numeral 4` y `eqc` usa `numeralM 4`, que son **dos constantes distintas**; pero con el índice
LITERAL las dos reducen a `succ⁴ zero`, así que `eqCodeFn a b` **es** `eqc a b` definicionalmente,
y `atom1CodeFn`/`atom2CodeFn` son `atomc` igual. No hace falta ningún puente.

Todo esto es composición pura de §6, §11 y §22-§24: **no hay nada nuevo que demostrar**. -/

/-! ### Listas de argumentos, por aridad -/

theorem prf_hasWitArgs_1 (x : Term) (hx : Prf (hasWit x)) :
    Prf (hasWitArgs (cons x nil)) :=
  prf_mp (prf_mp (prf_hasWitArgs_cons x nil) hx) prf_hasWitArgs_nil

theorem prf_hasWitArgs_2 (x y : Term) (hx : Prf (hasWit x)) (hy : Prf (hasWit y)) :
    Prf (hasWitArgs (cons x (cons y nil))) :=
  prf_mp (prf_mp (prf_hasWitArgs_cons x (cons y nil)) hx) (prf_hasWitArgs_1 y hy)

theorem prf_hasWitArgs_3 (x y z : Term)
    (hx : Prf (hasWit x)) (hy : Prf (hasWit y)) (hz : Prf (hasWit z)) :
    Prf (hasWitArgs (cons x (cons y (cons z nil)))) :=
  prf_mp (prf_mp (prf_hasWitArgs_cons x (cons y (cons z nil))) hx) (prf_hasWitArgs_2 y z hy hz)

/-! ### Sorte TÉRMINO: **todo** constructor dotado es un `funcc` -/

theorem prf_hasWit_funcc1 (S x : Term) (hx : Prf (hasWit x)) :
    Prf (hasWit (funcc S (cons x nil))) :=
  prf_mp (prf_hasWit_funcc S (cons x nil)) (prf_hasWitArgs_1 x hx)

theorem prf_hasWit_funcc2 (S x y : Term) (hx : Prf (hasWit x)) (hy : Prf (hasWit y)) :
    Prf (hasWit (funcc S (cons x (cons y nil)))) :=
  prf_mp (prf_hasWit_funcc S (cons x (cons y nil))) (prf_hasWitArgs_2 x y hx hy)

theorem prf_hasWit_funcc3 (S x y z : Term)
    (hx : Prf (hasWit x)) (hy : Prf (hasWit y)) (hz : Prf (hasWit z)) :
    Prf (hasWit (funcc S (cons x (cons y (cons z nil))))) :=
  prf_mp (prf_hasWit_funcc S (cons x (cons y (cons z nil)))) (prf_hasWitArgs_3 x y z hx hy hz)

/-- `liftc zero X` conserva testigo: es `CRIT_hasWit_lift`, en forma de aplicación. -/
theorem prf_hasWit_liftc {X : Term} (hX : Prf (hasWit X)) : Prf (hasWit (liftc zero X)) :=
  prf_mp (CRIT_hasWit_lift X) hX

/-! ### Sorte FÓRMULA: los ocho constructores, en forma de APLICACIÓN

Los de §22-§24 están en forma de implicación objeto —que es como los consume el paso de
inducción—; aguas abajo se usan aplicados, y con el tag ya fijado. -/

theorem prf_hasWitF_atom1 (P x : Term) (hx : Prf (hasWit x)) :
    Prf (hasWitF (atomc P (cons x nil))) :=
  prf_mp (prf_hasWitF_atomc P (cons x nil)) (prf_hasWitArgs_1 x hx)

theorem prf_hasWitF_atom2 (P x y : Term) (hx : Prf (hasWit x)) (hy : Prf (hasWit y)) :
    Prf (hasWitF (atomc P (cons x (cons y nil)))) :=
  prf_mp (prf_hasWitF_atomc P (cons x (cons y nil))) (prf_hasWitArgs_2 x y hx hy)

theorem prf_hasWitF_eq2 (a b : Term) (ha : Prf (hasWit a)) (hb : Prf (hasWit b)) :
    Prf (hasWitF (eqc a b)) :=
  prf_mp (prf_mp (prf_hasWitF_eqc a b) ha) hb

theorem prf_hasWitF_implc (a b : Term) (ha : Prf (hasWitF a)) (hb : Prf (hasWitF b)) :
    Prf (hasWitF (implc a b)) :=
  prf_mp (prf_mp (prf_hasWitF_bin 5 a b inj_bin5) ha) hb

theorem prf_hasWitF_andc (a b : Term) (ha : Prf (hasWitF a)) (hb : Prf (hasWitF b)) :
    Prf (hasWitF (andc a b)) :=
  prf_mp (prf_mp (prf_hasWitF_bin 7 a b inj_bin7) ha) hb

theorem prf_hasWitF_orc (a b : Term) (ha : Prf (hasWitF a)) (hb : Prf (hasWitF b)) :
    Prf (hasWitF (orc a b)) :=
  prf_mp (prf_mp (prf_hasWitF_bin 8 a b inj_bin8) ha) hb

theorem prf_hasWitF_forallc (a : Term) (ha : Prf (hasWitF a)) :
    Prf (hasWitF (forallc a)) :=
  prf_mp (prf_hasWitF_un 6 a inj_un6) ha

theorem prf_hasWitF_exc (a : Term) (ha : Prf (hasWitF a)) :
    Prf (hasWitF (exc a)) :=
  prf_mp (prf_hasWitF_un 9 a inj_un9) ha

/-! ### CONTROLES: el molde, sobre objetivos REALES del árbol

No son ejemplos de juguete: `tcFn (succ x)` es literalmente la forma que `NumCodeClosedPrf` usa
para el sucesor punteado, y `implc`/`eqc` sobre códigos punteados es lo que pide
`EvalBoundedPrf:237` — el único sitio de ③ cuyo código **no** es un `formCode`. -/

/-- El sucesor punteado, `funcc ⌜succ⌝ [x]`, con testigo. -/
example (x : Term) : Prf (hasWit (funcc (strCode "succ") (cons (tcFn x) nil))) :=
  prf_hasWit_funcc1 _ _ (prf_hasWit_tcFn x)

/-- Un constructor punteado BINARIO (`addcT`/`mulcT`/`nthcT`/`consT` son todos así). -/
example (x y : Term) :
    Prf (hasWit (funcc (strCode "add") (cons (tcFn x) (cons (tcFn y) nil)))) :=
  prf_hasWit_funcc2 _ _ _ (prf_hasWit_tcFn x) (prf_hasWit_tcFn y)

/-- La forma de `EvalBoundedPrf:237`: un nodo `implc` CONSTRUIDO, no un `formCode`. -/
example (x y : Term) (Phic : Term) (hP : Prf (hasWitF Phic)) :
    Prf (hasWitF (implc (eqc (tcFn x) (tcFn y)) Phic)) :=
  prf_hasWitF_implc _ _ (prf_hasWitF_eq2 _ _ (prf_hasWit_tcFn x) (prf_hasWit_tcFn y)) hP

end ROBINSON_PlusPlus.Meta.SubstfcWitnessPrf

export ROBINSON_PlusPlus.Meta.SubstfcWitnessPrf (
  prf_hasWit_substtc prf_hasWit_substtc_of_isTC1 prf_hasWitArgs_substtsc_of
  prf_hasWitF_substfc prf_hasWitF_substfc_mp prf_hasWitF_substfc_of_isFC1
  hasWitArgs liftF_hasWitArgs substF_hasWitArgs
  prf_wfAll1_nil prf_wfAllF_nil prf_hasWit_varc prf_lt_trich
  prf_in_nthc prf_in_concat prf_wfAll1_concat prf_wfAllF_concat
  prf_argsIn_nil prf_argsIn_mono_of prf_isTermCodeE1_mono_of prf_isFormCodeE2_mono_of
  prf_wfAllF_mono_wT prf_wfAllF_cons prf_argsIn_cons_intro
  prf_isTermCodeE1_func_imp prf_hasWit_funcc prf_hasWitArgs_nil prf_hasWitArgs_cons
  PrfH_congr_substtsc3 PrfH_congr_hasWitArgs PrfH_congr_hasWitF
  prf_imp_orL prf_imp_orR prf_imp_self prf_and_mono_right prf_inPair_mono_of
  binN unN prf_nthc_binN1 prf_nthc_binN2 prf_nthc_unN1
  prf_shapeBin_binN prf_shapeUn_unN prf_clBin_node prf_clUn_node
  prf_clUn_node_imp prf_clBin_node_imp
  inj_bot inj_atom inj_eq inj_bin5 inj_un6 inj_bin7 inj_bin8 inj_un9
  prf_hasWitF_imp prf_isFC1_unN prf_isFC1_binN prf_hasWitF_un prf_hasWitF_bin
  prf_hasWitF_bot prf_hasWitF_atomc prf_hasWitF_eqc
  prf_hasWitArgs_1 prf_hasWitArgs_2 prf_hasWitArgs_3
  prf_hasWit_funcc1 prf_hasWit_funcc2 prf_hasWit_funcc3 prf_hasWit_liftc
  prf_hasWitF_atom1 prf_hasWitF_atom2 prf_hasWitF_eq2
  prf_hasWitF_implc prf_hasWitF_andc prf_hasWitF_orc prf_hasWitF_forallc prf_hasWitF_exc
  nilOrCons nilOrCons_at prf_nil_or_cons_all prf_nil_or_cons
)


/-! ## FOOTPRINT -/
#print axioms ROBINSON_PlusPlus.Meta.SubstfcWitnessPrf.prf_hasWit_substtc
#print axioms ROBINSON_PlusPlus.Meta.SubstfcWitnessPrf.prf_hasWitF_substfc
#print axioms ROBINSON_PlusPlus.Meta.SubstfcWitnessPrf.prf_hasWitF_bin
#print axioms ROBINSON_PlusPlus.Meta.SubstfcWitnessPrf.prf_nil_or_cons
#print axioms ROBINSON_PlusPlus.Meta.SubstfcWitnessPrf.prf_hasWit_funcc2
#print axioms ROBINSON_PlusPlus.Meta.SubstfcWitnessPrf.prf_hasWitF_implc

/-
SONDEO (2026-09-06) — TAREA C, mitad TÉRMINO: `hasWit` es CERRADO bajo `substtc`.

## Por qué esta mitad primero

`prf_hasWitF_substfc` (lo único que separa el árbol del verde, §3.36.5) induce sobre el código de
FÓRMULA, y sus casos `atom`/`eq` tienen argumentos de sorte TÉRMINO: piden
`hasWit (substtc v s t)`. Medido el 09-06: **tampoco existe**. Así que C son DOS clausuras, y ésta
es el prerrequisito de la otra.

## El molde

`Meta/EvalLiftcPrf.lean` (rama B2) hizo exactamente esta forma para `liftc`: **UNA** inducción
fuerte con conclusión **CONJUNTIVA** sobre los dos sorts (término y lista de términos), y el
testigo cuantificado **dentro** de `Φ` (lo exige el gate `liftFormula 1 Φ = Φ`). Aquí hacen falta
**tres** binders —`w`, `v`, `s`— porque `substtc` lleva dos argumentos más que `liftc`.

⚠️ **LA MONEDA DE LA INDUCCIÓN OBJETO** (§3.31): las dos mitades van como implicación OBJETO
dentro de `Φ`. Un lema de caso con la HI como hipótesis META no sirve.

## Lo que ya está y esta mitad CONSUME

* `prf_wfAll1_cons` (`Meta/HasWitTcFnPrf.lean`, 09-05) — extender el testigo con un nodo.
* `prf_wfAll1_concat` (`sondeos/MergeTestigos.lean`, TAREA A, 09-06) — **FUSIONARLOS**, que es
  exactamente lo que pide el caso `cons` de la mitad de LISTA.
* `prf_argsIn_mono_of` / `prf_isTermCodeE1_mono_of` (TAREA A) — la monotonía generalizada.
* `CRIT_hasWit_lift` — la clausura bajo `liftc`, para cuando el binder sube el nivel.
* Las seis ecuaciones de `substtc`/`substtsc` en `Prf`: `Meta/ArithPrf.lean:130-171`.
-/

import ROBINSON_PlusPlus.Meta.HasWitTcFnPrf
import ROBINSON_PlusPlus.Meta.BoundedInPrf
import ROBINSON_PlusPlus.Meta.StrongInductionPrf
import ROBINSON_PlusPlus.Meta.SubstArith
import ROBINSON_PlusPlus.Meta.NumCodeClosedPrf
import ROBINSON_PlusPlus.Meta.CantorMonoPrf

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

namespace ClausuraSubsttc

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

`BODY w v s X` es el enunciado con TODO explícito; `PHI` lo cierra sobre los tres binders.
`#3` es el CÓDIGO sobre el que se induce; `#2` = `w`, `#1` = `v`, `#0` = `s`.

🔑 Los tres binders van DENTRO por el gate `liftFormula 1 Φ = Φ`, y la instanciación se colapsa
**paso a paso** (`PHI_spec1/2/3`), no con un `simp` final: con tres sustituciones anidadas el
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

def PHIbody : Formula := BODY (.var 2) (.var 1) (.var 0) (.var 3)

def PHI : Formula := Formula.forall (Formula.forall (Formula.forall PHIbody))

/-- **EL GATE de `prf_strong_induction`.** -/
theorem hPHI : liftFormula 1 PHI = PHI := by
  simp only [PHI, PHIbody, liftFormula, liftF_BODY, liftTerm, Nat.reduceAdd, Nat.reduceLT,
    reduceIte]

theorem PHI_at (t : Term) :
    substFormula 0 t PHI = Formula.forall (Formula.forall (Formula.forall
      (BODY (.var 2) (.var 1) (.var 0)
        (liftTerm 0 (liftTerm 0 (liftTerm 0 t)))))) := by
  simp only [PHI, PHIbody, substFormula, substF_BODY, substTerm, Nat.reduceAdd,
    Nat.reduceEqDiff, Nat.reduceGT, Nat.reduceSub, reduceIte, if_true]

/-! ### Los tres colapsos, uno por binder -/

theorem PHI_spec1 (t w : Term) :
    substFormula 0 w (Formula.forall (Formula.forall
      (BODY (.var 2) (.var 1) (.var 0) (liftTerm 0 (liftTerm 0 (liftTerm 0 t))))))
      = Formula.forall (Formula.forall
          (BODY (liftTerm 0 (liftTerm 0 w)) (.var 1) (.var 0)
            (liftTerm 0 (liftTerm 0 t)))) := by
  have h3 := substTerm_liftLiftLift t 0 (liftTerm 0 (liftTerm 0 w))
  simp only [substFormula, substF_BODY, substTerm, Nat.reduceAdd, Nat.reduceEqDiff,
    Nat.reduceGT, Nat.reduceSub, reduceIte, if_true, FOL.substTerm_liftTerm, h3]

theorem PHI_spec2 (t w v : Term) :
    substFormula 0 v (Formula.forall
      (BODY (liftTerm 0 (liftTerm 0 w)) (.var 1) (.var 0) (liftTerm 0 (liftTerm 0 t))))
      = Formula.forall (BODY (liftTerm 0 w) (liftTerm 0 v) (.var 0) (liftTerm 0 t)) := by
  have hw := FOL.substTerm_liftLift w 0 (liftTerm 0 v)
  have ht := FOL.substTerm_liftLift t 0 (liftTerm 0 v)
  simp only [substFormula, substF_BODY, substTerm, Nat.reduceAdd, Nat.reduceEqDiff,
    Nat.reduceGT, Nat.reduceSub, reduceIte, if_true, FOL.substTerm_liftTerm, hw, ht]

theorem PHI_spec3 (t w v s : Term) :
    substFormula 0 s (BODY (liftTerm 0 w) (liftTerm 0 v) (.var 0) (liftTerm 0 t))
      = BODY w v s t := by
  simp only [substF_BODY, substTerm, if_true, FOL.substTerm_liftTerm]

/-- Instanciación de los tres binders (`w`, `v`, `s`), en ese orden. -/
theorem PHI_use {Γ : List Formula} (t w v s : Term) (h : PrfH Γ (substFormula 0 t PHI)) :
    PrfH Γ (BODY w v s t) := by
  rw [PHI_at] at h
  have h1 := PrfH_spec h w
  rw [PHI_spec1] at h1
  have h2 := PrfH_spec h1 v
  rw [PHI_spec2] at h2
  have h3 := PrfH_spec h2 s
  rwa [PHI_spec3] at h3

/-! ## §3 · Sobre el paso

Molde: `Meta/EvalLiftcPrf.lean:396` (B2). La diferencia es que allí `PHI` tiene UN binder y aquí
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
def CTX1 : List Formula :=
  [land (isTC1 (.var 2) (.var 3)) (hasWit (.var 0)),
   liftFormula 0 (liftFormula 0 (liftFormula 0 (PSI PHI)))]

/-- El índice de la variable, cuando el código resulta ser un `varc`. -/
def NN : Term := nthc (.var 3) (numeralM 1)

/-- **El caso `varc`, aislado.** Del `shapeUn` y las hipótesis sale el testigo del sustituido. -/
theorem caso_varc :
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
hipótesis de inducción con `PSI_inst3` —**tres** lifts, porque `PHI` tiene tres binders; la
escalera psi que B3 promovió— y monta el nodo sustituido con §6. -/

/-- El símbolo y los argumentos, cuando el código resulta ser un `funcc`. -/
def SS : Term := nthc (.var 3) (numeralM 1)
def AA : Term := nthc (.var 3) (numeralM 2)

theorem caso_funcc :
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
      (liftFormula 0 (liftFormula 0 (liftFormula 0 (PSI PHI)))) :=
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
  have hih := PrfH.mp _ _ _ (PSI_inst3 PHI hPHI hpsi AA) hltb
  have huse := PHI_use AA (.var 2) (.var 1) (.var 0) hih
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
def CTXa (W a as : Term) : List Formula :=
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
def CTX2 : List Formula :=
  [land (land (wfAll1 (.var 2)) (argsIn (.var 2) (.var 3))) (hasWit (.var 0)),
   liftFormula 0 (liftFormula 0 (liftFormula 0 (PSI PHI)))]

/-- **El caso `nil` de la mitad de LISTA.** -/
theorem caso_nil :
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
def CTXc (W₁ W₂ : Term) : List Formula :=
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

def HD : Term := carc (.var 3)
def TL : Term := cdrc (.var 3)

theorem caso_cons :
    PrfH (consOk (.var 3) :: CTX2) (hasWitArgs (substtsc (.var 1) (.var 0) (.var 3))) := by
  have hcons : PrfH (consOk (.var 3) :: CTX2) (consOk (.var 3)) := PrfH.hyp _ _ (List.Mem.head _)
  have hh : PrfH (consOk (.var 3) :: CTX2)
      (land (land (wfAll1 (.var 2)) (argsIn (.var 2) (.var 3))) (hasWit (.var 0))) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hpsi : PrfH (consOk (.var 3) :: CTX2)
      (liftFormula 0 (liftFormula 0 (liftFormula 0 (PSI PHI)))) :=
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
  have hihHD := PrfH.mp _ _ _ (PSI_inst3 PHI hPHI hpsi HD) hltHD
  have huseHD := PHI_use HD (.var 2) (.var 1) (.var 0) hihHD
  have hHD := PrfH.mp _ _ _ (PrfH_and_elim_left huseHD)
    (PrfH_and_intro (PrfH_and_intro hwf hinHD) hws)
  have hihTL := PrfH.mp _ _ _ (PSI_inst3 PHI hPHI hpsi TL) hltTL
  have huseTL := PHI_use TL (.var 2) (.var 1) (.var 0) hihTL
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

theorem PHI_step : Prf (Formula.forall (Formula.impl (PSI PHI) PHI)) := by
  refine Prf.gen _ (prf_deduction ?_)
  refine PrfH.gen [PSI PHI] _ ?_
  simp only [List.map_cons, List.map_nil]
  refine PrfH.gen _ _ ?_
  simp only [List.map_cons, List.map_nil]
  refine PrfH.gen _ _ ?_
  simp only [List.map_cons, List.map_nil]
  refine PrfH_and_intro ?half1 ?half2
  case half1 =>
    refine deduction_aux ?_ (land (isTC1 (.var 2) (.var 3)) (hasWit (.var 0)))
      [liftFormula 0 (liftFormula 0 (liftFormula 0 (PSI PHI)))] rfl
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
      [liftFormula 0 (liftFormula 0 (liftFormula 0 (PSI PHI)))] rfl
    exact PrfH_or_elim (prf_to_prfH (prf_nil_or_cons (.var 3)) _) caso_nil caso_cons

theorem PHI_all (t : Term) : Prf (substFormula 0 t PHI) :=
  prf_strong_induction PHI hPHI PHI_step t

/-- **LA CLAUSURA, con testigo EXPLÍCITO** (la forma que sale de la inducción). -/
theorem prf_hasWit_substtc_of_isTC1 (w v s t : Term) :
    Prf (Formula.impl (land (isTC1 w t) (hasWit s)) (hasWit (substtc v s t))) :=
  prfH_nil_to_prf (PrfH_and_elim_left (PHI_use t w v s (prf_to_prfH (PHI_all t) []))) rfl

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

/-! ## §14 · FOOTPRINT -/
#print axioms ClausuraSubsttc.prf_hasWit_substtc_of_isTC1
#print axioms ClausuraSubsttc.prf_hasWit_substtc

/-! ## §15 · La mitad de LISTA, expuesta

La mitad 2 de la inducción, en forma consumible. Es lo que los casos `atom` (lista de argumentos)
de la mitad de FÓRMULA van a necesitar. -/

theorem prf_hasWitArgs_substtsc_of (w v s Y : Term) :
    Prf (Formula.impl (land (land (wfAll1 w) (argsIn w Y)) (hasWit s))
      (hasWitArgs (substtsc v s Y))) :=
  prfH_nil_to_prf (PrfH_and_elim_right (PHI_use Y w v s (prf_to_prfH (PHI_all Y) []))) rfl

/-! ## §16 · MITAD FÓRMULA — el armazón

`hasWitF` lleva DOS listas testigo (`wF` de fórmulas, `wT` de términos contra la que se valida),
así que `PHI` tiene **cuatro** binders: `wF`(#3), `wT`(#2), `v`(#1), `s`(#0), y el código es `#4`.
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

def PHIFbody : Formula := BODYF (.var 3) (.var 2) (.var 1) (.var 0) (.var 4)

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

end ClausuraSubsttc

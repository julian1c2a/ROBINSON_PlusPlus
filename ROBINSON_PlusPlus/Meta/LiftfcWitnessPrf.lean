/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.EvalLiftfcPrf

/-!
# La CLAUSURA de las guardas bajo el LIFT OBJETO — `liftc`, `liftsc` y `liftfc`

Es el análogo de `Meta/SubstfcWitnessPrf.lean` (rama C de [ADR-020](../../DECISIONS.md)) para la
familia del **lift**, y salda la deuda que `Meta/EvalLiftfcPrf.lean` §12 dejó enunciada
(`DEUDA_hasWitF_liftfc`):

```
prf_hasWit_liftc_at   (v t) : Prf (hasWit t  ⇒ hasWit  (liftc  v t))
prf_hasWitArgs_liftsc (v Y) : Prf (hasWitArgs Y ⇒ hasWitArgs (liftsc v Y))   -- vía la conjuntiva
prf_hasWitF_liftfc    (v X) : Prf (hasWitF X ⇒ hasWitF (liftfc v X))
```

⭐ Con ellas, `ind` (18) y `listInd` (20) —los dos reflectores de sustitución que le faltaban a
C3— dejan de estar bloqueados, y con ellos `hbody`(a) de D3 (§3.54.1).

## Por qué sale MÁS BARATO que el molde, y dónde exactamente

Igual que `pcc_eval_liftfc` salió un binder más barato que `pcc_eval_substfc`, aquí hay **tres**
ahorros medidos, y el primero es el grande:

1. ⭐⭐ **El caso `varc` deja de ser una tricotomía con rama cara.** En `substtc`, una de las tres
   ramas devuelve **el sustituyendo** `s`, y su testigo hay que arrastrarlo por toda la inducción
   (de ahí el binder `s` y la hipótesis `hasWit s`). En `liftc` **las dos ramas devuelven un
   `varc`** —`varc n` o `varc (succ n)`—, y `prf_hasWit_varc` es **incondicional**. ⇒ ni binder
   `s`, ni guarda, ni transporte.
2. **Un binder menos en el armazón**: `PHIL` tiene DOS (`w`, `v`) frente a los tres de `PHIT`, y
   `PHILF` tiene TRES frente a los cuatro de `PHIF`. La escalera que toca es `PSI_inst2`/`PSI_inst3`.
3. ⭐ **Toda la maquinaria genérica se reutiliza tal cual** (ADR-019): `hasWitArgs`,
   `prf_hasWit_varc`, `prf_hasWit_funcc`, `prf_hasWitArgs_nil`/`_cons`, `prf_hasWitF_bot`/`_atomc`/
   `_eqc`, `prf_hasWitF_un`/`_bin` y las ocho inyecciones salen **exportadas** de
   `SubstfcWitnessPrf`. Este módulo sólo escribe lo que es específico del lift.

## ⚠️ Lo que NO se abarata: el NIVEL viaja dentro de `Φ`

Los casos `forallc`/`exc` **suben el nivel** (`liftfc c (forallc a) ≐ forallc (liftfc (σc) a)`), así
que la hipótesis de inducción hace falta a un nivel **distinto** del que se concluye. ⇒ `v` va
**cuantificado dentro de `Φ`**, exactamente por la misma razón que en el chasis de
`pcc_eval_liftfc` (§3.53.3) y en A5.

**Footprint**: `[propext, Classical.choice, Quot.sound]` — net-0 puro.
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
open ROBINSON_PlusPlus.Meta.NumCodeClosedPrf
open ROBINSON_PlusPlus.Meta.CantorMonoPrf
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf.ENS
open ROBINSON_PlusPlus.Meta.HasWitTcFnPrf
open ROBINSON_PlusPlus.Meta.SubstArith
open ROBINSON_PlusPlus.Meta.SubstfcWitnessPrf
open ROBINSON_PlusPlus.Meta.LiftcCodePrf
open ROBINSON_PlusPlus.Meta.EvalLiftfcPrf

set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000

namespace ROBINSON_PlusPlus.Meta.LiftfcWitnessPrf

/-! ## §1 · Las congruencias del lift que no existían

`PrfH_congr_liftc` está en `ChainPrf`; sus dos hermanas —lista y fórmula— no. Mismo molde de
Leibniz objeto que `PrfH_congr_substtsc3`. -/

theorem PrfH_congr_liftsc {Γ : List Formula} {c a b : Term} (h : PrfH Γ (a =eq b)) :
    PrfH Γ (liftsc c a =eq liftsc c b) := by
  let f : Formula := Formula.eq (liftsc (liftTerm 0 c) (liftTerm 0 a))
                                (liftsc (liftTerm 0 c) (.var 0))
  have hS : ∀ x : Term, substFormula 0 x f = Formula.eq (liftsc c a) (liftsc c x) := by
    intro x
    simp only [f, liftsc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  have h0 : PrfH Γ (substFormula 0 a f) := by rw [hS a]; exact prf_to_prfH (prf_refl _) _
  have h1 := PrfH_leibniz_subst (A := f) h h0
  rwa [hS b] at h1

theorem PrfH_congr_liftfc {Γ : List Formula} {c a b : Term} (h : PrfH Γ (a =eq b)) :
    PrfH Γ (liftfc c a =eq liftfc c b) := by
  let f : Formula := Formula.eq (liftfc (liftTerm 0 c) (liftTerm 0 a))
                                (liftfc (liftTerm 0 c) (.var 0))
  have hS : ∀ x : Term, substFormula 0 x f = Formula.eq (liftfc c a) (liftfc c x) := by
    intro x
    simp only [f, liftfc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  have h0 : PrfH Γ (substFormula 0 a f) := by rw [hS a]; exact prf_to_prfH (prf_refl _) _
  have h1 := PrfH_leibniz_subst (A := f) h h0
  rwa [hS b] at h1

/-! ## §2 · EL ARMAZÓN de la mitad TÉRMINO

`BODYL w v X` es el enunciado con todo explícito; `PHIL` lo cierra sobre **dos** binders.
`#2` es el CÓDIGO sobre el que se induce; `#1` = `w`, `#0` = `v`.

⚠️ El binder `v` va **dentro** por la razón del preámbulo (los `forallc`/`exc` de la mitad de
FÓRMULA lo cambian), y `w` por el gate `liftFormula 1 Φ = Φ`. -/

def BODYL (w v X : Term) : Formula :=
  land (Formula.impl (isTC1 w X) (hasWit (liftc v X)))
       (Formula.impl (land (wfAll1 w) (argsIn w X)) (hasWitArgs (liftsc v X)))

theorem liftF_BODYL (k : Nat) (w v X : Term) :
    liftFormula k (BODYL w v X)
      = BODYL (liftTerm k w) (liftTerm k v) (liftTerm k X) := by
  simp only [BODYL, land, liftFormula, liftF_isTC1, liftF_wfAll1, liftF_argsIn, liftF_hasWit,
    liftF_hasWitArgs, liftc, liftsc, liftTerm, liftTerms]

theorem substF_BODYL (k : Nat) (u w v X : Term) :
    substFormula k u (BODYL w v X)
      = BODYL (substTerm k u w) (substTerm k u v) (substTerm k u X) := by
  simp only [BODYL, land, substFormula, substF_isTC1, substF_wfAll1, substF_argsIn, substF_hasWit,
    substF_hasWitArgs, liftc, liftsc, substTerm, substTerms]

private def PHILbody : Formula := BODYL (.var 1) (.var 0) (.var 2)

def PHIL : Formula := Formula.forall (Formula.forall PHILbody)

/-- **EL GATE de `prf_strong_induction`.** -/
theorem hPHIL : liftFormula 1 PHIL = PHIL := by
  simp only [PHIL, PHILbody, liftFormula, liftF_BODYL, liftTerm, Nat.reduceAdd, Nat.reduceLT,
    reduceIte]

theorem PHIL_at (t : Term) :
    substFormula 0 t PHIL = Formula.forall (Formula.forall
      (BODYL (.var 1) (.var 0) (liftTerm 0 (liftTerm 0 t)))) := by
  simp only [PHIL, PHILbody, substFormula, substF_BODYL, substTerm, Nat.reduceAdd,
    Nat.reduceEqDiff, Nat.reduceGT, Nat.reduceSub, reduceIte, if_true]

theorem PHIL_spec1 (t w : Term) :
    substFormula 0 w (Formula.forall (BODYL (.var 1) (.var 0) (liftTerm 0 (liftTerm 0 t))))
      = Formula.forall (BODYL (liftTerm 0 w) (.var 0) (liftTerm 0 t)) := by
  have ht := FOL.substTerm_liftLift t 0 (liftTerm 0 w)
  simp only [substFormula, substF_BODYL, substTerm, Nat.reduceAdd, Nat.reduceEqDiff,
    Nat.reduceGT, Nat.reduceSub, reduceIte, if_true, FOL.substTerm_liftTerm, ht]

theorem PHIL_spec2 (t w v : Term) :
    substFormula 0 v (BODYL (liftTerm 0 w) (.var 0) (liftTerm 0 t)) = BODYL w v t := by
  simp only [substF_BODYL, substTerm, if_true, FOL.substTerm_liftTerm]

/-- Instanciación de los dos binders (`w`, `v`), en ese orden. -/
theorem PHIL_use {Γ : List Formula} (t w v : Term) (h : PrfH Γ (substFormula 0 t PHIL)) :
    PrfH Γ (BODYL w v t) := by
  rw [PHIL_at] at h
  have h1 := PrfH_spec h w
  rw [PHIL_spec1] at h1
  have h2 := PrfH_spec h1 v
  rwa [PHIL_spec2] at h2

/-! ## §3 · EL PASO, mitad TÉRMINO — caso `varc`

⭐⭐ **Aquí está el ahorro grande.** `prf_liftc_varc_cases` parte en DOS (no tres), y **las dos
ramas devuelven un `varc`**: `varc n` si el índice está por debajo del nivel, `varc (succ n)` si
no. `prf_hasWit_varc` es **incondicional**, así que no hay testigo que arrastrar. -/

/-- Contexto de la mitad TÉRMINO tras introducir su antecedente. -/
private def CTX1 : List Formula :=
  [isTC1 (.var 1) (.var 2),
   liftFormula 0 (liftFormula 0 (PSI PHIL))]

/-- El índice de la variable, cuando el código resulta ser un `varc`. -/
private def NN : Term := nthc (.var 2) (numeralM 1)

private theorem caso_varc :
    PrfH (shapeUn (.var 2) 0 :: CTX1) (hasWit (liftc (.var 0) (.var 2))) := by
  have hshape : PrfH (shapeUn (.var 2) 0 :: CTX1) (shapeUn (.var 2) 0) :=
    PrfH.hyp _ _ (List.Mem.head _)
  refine PrfH_or_elim (prf_to_prfH (prf_liftc_varc_cases (.var 0) NN) _) ?c_lt ?c_ge
  case c_lt =>
    -- `NN < v`: el lift NO toca la variable
    have hlt : PrfH (lt NN (.var 0) :: shapeUn (.var 2) 0 :: CTX1) (lt NN (.var 0)) :=
      PrfH.hyp _ _ (List.Mem.head _)
    have hs2 : PrfH (lt NN (.var 0) :: shapeUn (.var 2) 0 :: CTX1)
        (liftc (.var 0) (.var 2) =eq liftc (.var 0) (varc NN)) :=
      PrfH_congr_liftc (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))
    have heq := PrfH.mp _ _ _
      (prf_to_prfH (prf_liftc_var_lt (.var 0) NN) _) hlt
    exact PrfH_congr_hasWit (PrfH_eq_symm (PrfH_eq_trans hs2 heq))
      (prf_to_prfH (prf_hasWit_varc NN) _)
  case c_ge =>
    -- `v < σNN`: el lift la SUBE, y sigue siendo un `varc`
    have hge : PrfH (lt (.var 0) (succ NN) :: shapeUn (.var 2) 0 :: CTX1)
        (lt (.var 0) (succ NN)) := PrfH.hyp _ _ (List.Mem.head _)
    have hs2 : PrfH (lt (.var 0) (succ NN) :: shapeUn (.var 2) 0 :: CTX1)
        (liftc (.var 0) (.var 2) =eq liftc (.var 0) (varc NN)) :=
      PrfH_congr_liftc (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))
    have heq := PrfH.mp _ _ _
      (prf_to_prfH (prf_liftc_var_ge (.var 0) NN) _) hge
    exact PrfH_congr_hasWit (PrfH_eq_symm (PrfH_eq_trans hs2 heq))
      (prf_to_prfH (prf_hasWit_varc (succ NN)) _)

/-! ## §4 · EL PASO, mitad TÉRMINO — caso `funcc`

Idéntico al molde salvo por el operador: cadena de Cantor, `PSI_inst2` (dos binders) y el nodo
lifteado con `prf_hasWit_funcc`. -/

private def SS : Term := nthc (.var 2) (numeralM 1)
private def AA : Term := nthc (.var 2) (numeralM 2)

private theorem caso_funcc :
    PrfH (land (shapeBin (.var 2) 1) (argsIn (.var 1) AA) :: CTX1)
      (hasWit (liftc (.var 0) (.var 2))) := by
  have hb : PrfH (land (shapeBin (.var 2) 1) (argsIn (.var 1) AA) :: CTX1)
      (land (shapeBin (.var 2) 1) (argsIn (.var 1) AA)) := PrfH.hyp _ _ (List.Mem.head _)
  have hshape := PrfH_and_elim_left hb
  have hargs := PrfH_and_elim_right hb
  have hh : PrfH (land (shapeBin (.var 2) 1) (argsIn (.var 1) AA) :: CTX1)
      (isTC1 (.var 1) (.var 2)) := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hwf := PrfH_and_elim_left hh
  have hpsi : PrfH (land (shapeBin (.var 2) 1) (argsIn (.var 1) AA) :: CTX1)
      (liftFormula 0 (liftFormula 0 (PSI PHIL))) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  -- (1) la CADENA DE CANTOR
  have h1 : Prf (lt AA (cons AA nil)) := prf_cantor_mono_left _ _
  have h2 : Prf (lt (cons AA nil) (cons SS (cons AA nil))) := prf_cantor_mono_right _ _
  have h3 : Prf (lt (cons SS (cons AA nil))
      (cons (numeralM 1) (cons SS (cons AA nil)))) := prf_cantor_mono_right _ _
  have h12 : Prf (lt AA (cons SS (cons AA nil))) :=
    prf_mp (prf_mp (prf_lt_trans _ _ _) h1) h2
  have h123 : Prf (lt AA (cons (numeralM 1) (cons SS (cons AA nil)))) :=
    prf_mp (prf_mp (prf_lt_trans _ _ _) h12) h3
  have hltb := PrfH_lt_subst2 (PrfH_eq_symm hshape) (prf_to_prfH h123 _)
  -- (2) la HIPOTESIS DE INDUCCION en el argumento
  have hih := PrfH.mp _ _ _ (PSI_inst2 PHIL hPHIL hpsi AA) hltb
  have huse := PHIL_use AA (.var 1) (.var 0) hih
  have hargsW := PrfH.mp _ _ _ (PrfH_and_elim_right huse) (PrfH_and_intro hwf hargs)
  -- (3) el nodo lifteado tiene testigo
  have hnode := PrfH.mp _ _ _
    (prf_to_prfH (prf_hasWit_funcc SS (liftsc (.var 0) AA)) _) hargsW
  -- (4) y se transporta al codigo original
  have hs1 : PrfH (land (shapeBin (.var 2) 1) (argsIn (.var 1) AA) :: CTX1)
      (liftc (.var 0) (.var 2) =eq liftc (.var 0) (funcc SS AA)) :=
    PrfH_congr_liftc hshape
  have hs2 : PrfH (land (shapeBin (.var 2) 1) (argsIn (.var 1) AA) :: CTX1)
      (liftc (.var 0) (funcc SS AA) =eq funcc SS (liftsc (.var 0) AA)) :=
    prf_to_prfH (prf_liftc_func (.var 0) SS AA) _
  exact PrfH_congr_hasWit (PrfH_eq_symm (PrfH_eq_trans hs1 hs2)) hnode

/-! ## §5 · EL PASO, mitad LISTA — casos `nil` y `cons` -/

private def CTX2 : List Formula :=
  [land (wfAll1 (.var 1)) (argsIn (.var 1) (.var 2)),
   liftFormula 0 (liftFormula 0 (PSI PHIL))]

private theorem caso_nil :
    PrfH (Formula.eq (.var 2) nil :: CTX2) (hasWitArgs (liftsc (.var 0) (.var 2))) := by
  have heq : PrfH (Formula.eq (.var 2) nil :: CTX2) (Formula.eq (.var 2) nil) :=
    PrfH.hyp _ _ (List.Mem.head _)
  have h1 : PrfH (Formula.eq (.var 2) nil :: CTX2)
      (liftsc (.var 0) (.var 2) =eq liftsc (.var 0) nil) := PrfH_congr_liftsc heq
  have h2 : PrfH (Formula.eq (.var 2) nil :: CTX2) (liftsc (.var 0) nil =eq nil) :=
    prf_to_prfH (prf_liftsc_nil (.var 0)) _
  exact PrfH_congr_hasWitArgs (PrfH_eq_symm (PrfH_eq_trans h1 h2))
    (prf_to_prfH prf_hasWitArgs_nil _)

private def HD : Term := carc (.var 2)
private def TL : Term := cdrc (.var 2)

private theorem caso_cons :
    PrfH (consOk (.var 2) :: CTX2) (hasWitArgs (liftsc (.var 0) (.var 2))) := by
  have hcons : PrfH (consOk (.var 2) :: CTX2) (consOk (.var 2)) := PrfH.hyp _ _ (List.Mem.head _)
  have hh : PrfH (consOk (.var 2) :: CTX2) (land (wfAll1 (.var 1)) (argsIn (.var 1) (.var 2))) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hpsi : PrfH (consOk (.var 2) :: CTX2) (liftFormula 0 (liftFormula 0 (PSI PHIL))) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  have hwf := PrfH_and_elim_left hh
  have hargs0 := PrfH_and_elim_right hh
  -- (1) partir la lista y su `argsIn`
  have hargs : PrfH (consOk (.var 2) :: CTX2) (argsIn (.var 1) (cons HD TL)) :=
    PrfH_congr_argsIn hcons hargs0
  have hinHD := PrfH.mp _ _ _ (prf_to_prfH (prf_argsIn_head (.var 1) HD TL) _) hargs
  have hargsTL := PrfH.mp _ _ _ (prf_to_prfH (prf_argsIn_tail (.var 1) HD TL) _) hargs
  -- (2) Cantor
  have hcHD : Prf (lt HD (cons HD TL)) := prf_cantor_mono_left _ _
  have hcTL : Prf (lt TL (cons HD TL)) := prf_cantor_mono_right _ _
  have hltHD := PrfH_lt_subst2 (PrfH_eq_symm hcons) (prf_to_prfH hcHD _)
  have hltTL := PrfH_lt_subst2 (PrfH_eq_symm hcons) (prf_to_prfH hcTL _)
  -- (3) la HI en cada mitad
  have hihHD := PrfH.mp _ _ _ (PSI_inst2 PHIL hPHIL hpsi HD) hltHD
  have huseHD := PHIL_use HD (.var 1) (.var 0) hihHD
  have hHD := PrfH.mp _ _ _ (PrfH_and_elim_left huseHD) (PrfH_and_intro hwf hinHD)
  have hihTL := PrfH.mp _ _ _ (PSI_inst2 PHIL hPHIL hpsi TL) hltTL
  have huseTL := PHIL_use TL (.var 1) (.var 0) hihTL
  have hTL := PrfH.mp _ _ _ (PrfH_and_elim_right huseTL) (PrfH_and_intro hwf hargsTL)
  -- (4) la FUSION
  have hfus := PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (prf_hasWitArgs_cons
    (liftc (.var 0) HD) (liftsc (.var 0) TL)) _) hHD) hTL
  -- (5) transporte
  have h1 : PrfH (consOk (.var 2) :: CTX2)
      (liftsc (.var 0) (.var 2) =eq liftsc (.var 0) (cons HD TL)) := PrfH_congr_liftsc hcons
  have h2 : PrfH (consOk (.var 2) :: CTX2)
      (liftsc (.var 0) (cons HD TL) =eq cons (liftc (.var 0) HD) (liftsc (.var 0) TL)) :=
    prf_to_prfH (prf_liftsc_cons (.var 0) HD TL) _
  exact PrfH_congr_hasWitArgs (PrfH_eq_symm (PrfH_eq_trans h1 h2)) hfus

/-! ## §6 · EL PASO ENSAMBLADO, y el resultado de la mitad TÉRMINO -/

theorem PHIL_step : Prf (Formula.forall (Formula.impl (PSI PHIL) PHIL)) := by
  refine Prf.gen _ (prf_deduction ?_)
  refine PrfH.gen [PSI PHIL] _ ?_
  simp only [List.map_cons, List.map_nil]
  refine PrfH.gen _ _ ?_
  simp only [List.map_cons, List.map_nil]
  refine PrfH_and_intro ?half1 ?half2
  case half1 =>
    refine deduction_aux ?_ (isTC1 (.var 1) (.var 2))
      [liftFormula 0 (liftFormula 0 (PSI PHIL))] rfl
    have hh : PrfH CTX1 (isTC1 (.var 1) (.var 2)) := PrfH.hyp _ _ (List.Mem.head _)
    have hwf := PrfH_and_elim_left hh
    have hin := PrfH_and_elim_right hh
    have hnode := PrfH.mp _ _ _ (PrfH.mp _ _ _
      (prf_to_prfH (prf_isTermCodeE1_of_In (.var 1) (.var 2)) _) hin) hwf
    exact PrfH_or_elim hnode caso_varc caso_funcc
  case half2 =>
    refine deduction_aux ?_ (land (wfAll1 (.var 1)) (argsIn (.var 1) (.var 2)))
      [liftFormula 0 (liftFormula 0 (PSI PHIL))] rfl
    exact PrfH_or_elim (prf_to_prfH (prf_nil_or_cons (.var 2)) _) caso_nil caso_cons

theorem PHIL_all (t : Term) : Prf (substFormula 0 t PHIL) :=
  prf_strong_induction PHIL hPHIL PHIL_step t

/-- **LA CLAUSURA DE TÉRMINO, con testigo EXPLÍCITO.** -/
theorem prf_hasWit_liftc_of_isTC1 (w v t : Term) :
    Prf (Formula.impl (isTC1 w t) (hasWit (liftc v t))) :=
  prfH_nil_to_prf (PrfH_and_elim_left (PHIL_use t w v (prf_to_prfH (PHIL_all t) []))) rfl

/-- 🏁 **LA CLAUSURA DEL SORTE TÉRMINO**: `hasWit` es cerrado bajo `liftc`, **a nivel arbitrario**.
    ⭐ Generaliza `prf_hasWit_liftc` (`SubstfcWitnessPrf`), que sólo cubría el nivel `zero`. -/
theorem prf_hasWit_liftc_at (v t : Term) :
    Prf (Formula.impl (hasWit t) (hasWit (liftc v t))) := by
  refine prf_ex_elim_imp ?_
  have hg : liftFormula 0 (hasWit (liftc v t))
      = hasWit (liftc (liftTerm 0 v) (liftTerm 0 t)) := by
    simp only [liftF_hasWit, liftc, liftTerm, liftTerms]
  rw [hg]
  exact PrfH.mp _ _ _
    (prf_to_prfH (prf_hasWit_liftc_of_isTC1 (.var 0) (liftTerm 0 v) (liftTerm 0 t)) _)
    (prfH_hyp_self _)

/-- La mitad de LISTA, expuesta: es lo que el caso `atomc` de la mitad de FÓRMULA consume. -/
theorem prf_hasWitArgs_liftsc_of (w v Y : Term) :
    Prf (Formula.impl (land (wfAll1 w) (argsIn w Y)) (hasWitArgs (liftsc v Y))) :=
  prfH_nil_to_prf (PrfH_and_elim_right (PHIL_use Y w v (prf_to_prfH (PHIL_all Y) []))) rfl

/-! ## §7 · MITAD FÓRMULA — el armazón

`hasWitF` lleva DOS listas testigo (`wF` de fórmulas, `wT` de términos), así que `PHILF` tiene
**TRES** binders: `wF`(#2), `wT`(#1), `v`(#0), y el código es `#3`. Uno menos que `PHIF`, porque
no hay sustituyendo.

⚠️ Como en el molde, el cuerpo **no es conjuntivo**: la parte de lista ya está resuelta en §6 y
entra como lema externo. -/

def BODYFL (wF wT v X : Term) : Formula :=
  Formula.impl (isFC1 wF wT X) (hasWitF (liftfc v X))

theorem liftF_BODYFL (k : Nat) (wF wT v X : Term) :
    liftFormula k (BODYFL wF wT v X)
      = BODYFL (liftTerm k wF) (liftTerm k wT) (liftTerm k v) (liftTerm k X) := by
  simp only [BODYFL, liftFormula, liftF_isFC1, liftF_hasWitF, liftfc, liftTerm, liftTerms]

theorem substF_BODYFL (k : Nat) (u wF wT v X : Term) :
    substFormula k u (BODYFL wF wT v X)
      = BODYFL (substTerm k u wF) (substTerm k u wT) (substTerm k u v) (substTerm k u X) := by
  simp only [BODYFL, substFormula, substF_isFC1, substF_hasWitF, liftfc, substTerm, substTerms]

private def PHILFbody : Formula := BODYFL (.var 2) (.var 1) (.var 0) (.var 3)

def PHILF : Formula := Formula.forall (Formula.forall (Formula.forall PHILFbody))

theorem hPHILF : liftFormula 1 PHILF = PHILF := by
  simp only [PHILF, PHILFbody, liftFormula, liftF_BODYFL, liftTerm, Nat.reduceAdd,
    Nat.reduceLT, reduceIte]

theorem PHILF_at (t : Term) :
    substFormula 0 t PHILF = Formula.forall (Formula.forall (Formula.forall
      (BODYFL (.var 2) (.var 1) (.var 0)
        (liftTerm 0 (liftTerm 0 (liftTerm 0 t)))))) := by
  simp only [PHILF, PHILFbody, substFormula, substF_BODYFL, substTerm, Nat.reduceAdd,
    Nat.reduceEqDiff, Nat.reduceGT, Nat.reduceSub, reduceIte, if_true]

theorem PHILF_spec1 (t wF : Term) :
    substFormula 0 wF (Formula.forall (Formula.forall
      (BODYFL (.var 2) (.var 1) (.var 0) (liftTerm 0 (liftTerm 0 (liftTerm 0 t))))))
      = Formula.forall (Formula.forall
          (BODYFL (liftTerm 0 (liftTerm 0 wF)) (.var 1) (.var 0)
            (liftTerm 0 (liftTerm 0 t)))) := by
  have h3 := substTerm_liftLiftLift t 0 (liftTerm 0 (liftTerm 0 wF))
  simp only [substFormula, substF_BODYFL, substTerm, Nat.reduceAdd, Nat.reduceEqDiff,
    Nat.reduceGT, Nat.reduceSub, reduceIte, if_true, FOL.substTerm_liftTerm, h3]

theorem PHILF_spec2 (t wF wT : Term) :
    substFormula 0 wT (Formula.forall
      (BODYFL (liftTerm 0 (liftTerm 0 wF)) (.var 1) (.var 0) (liftTerm 0 (liftTerm 0 t))))
      = Formula.forall (BODYFL (liftTerm 0 wF) (liftTerm 0 wT) (.var 0) (liftTerm 0 t)) := by
  have hw := FOL.substTerm_liftLift wF 0 (liftTerm 0 wT)
  have ht := FOL.substTerm_liftLift t 0 (liftTerm 0 wT)
  simp only [substFormula, substF_BODYFL, substTerm, Nat.reduceAdd, Nat.reduceEqDiff,
    Nat.reduceGT, Nat.reduceSub, reduceIte, if_true, FOL.substTerm_liftTerm, hw, ht]

theorem PHILF_spec3 (t wF wT v : Term) :
    substFormula 0 v (BODYFL (liftTerm 0 wF) (liftTerm 0 wT) (.var 0) (liftTerm 0 t))
      = BODYFL wF wT v t := by
  simp only [substF_BODYFL, substTerm, if_true, FOL.substTerm_liftTerm]

theorem PHILF_use {Γ : List Formula} (t wF wT v : Term)
    (h : PrfH Γ (substFormula 0 t PHILF)) : PrfH Γ (BODYFL wF wT v t) := by
  rw [PHILF_at] at h
  have h1 := PrfH_spec h wF
  rw [PHILF_spec1] at h1
  have h2 := PrfH_spec h1 wT
  rw [PHILF_spec2] at h2
  have h3 := PrfH_spec h2 v
  rwa [PHILF_spec3] at h3

/-! ## §8 · EL PASO de la mitad FÓRMULA — los OCHO casos

Mismo reparto que el molde: `bot` inmediato; `atom` y `eq` consumen la mitad TÉRMINO (§6) y **no
inducen**; los tres `bin` (5/7/8) y los dos `un` (6/9) usan la HI con la escalera de Cantor.

⭐ Y aquí se nota otra vez el ahorro: los casos `un` **no necesitan `CRIT_hasWit_lift`**. En el
molde el sustituyendo sube de nivel al entrar en el binder y hay que darle testigo; aquí lo único
que sube es el **nivel**, que no lleva guarda. -/

private def AF : Term := nthc (.var 3) (numeralM 1)
private def BF : Term := nthc (.var 3) (numeralM 2)

private theorem casoF_bot {Γ : List Formula} (hcl : PrfH Γ (clBot (.var 3))) :
    PrfH Γ (hasWitF (liftfc (.var 0) (.var 3))) := by
  have heq : PrfH Γ (liftfc (.var 0) (.var 3) =eq botc) :=
    PrfH_eq_trans (PrfH_congr_liftfc hcl)
      (prf_to_prfH (prf_liftfc_bottom (.var 0)) _)
  exact PrfH_congr_hasWitF (PrfH_eq_symm heq) (prf_to_prfH prf_hasWitF_bot _)

private theorem casoF_atom {Γ : List Formula} (hcl : PrfH Γ (clAtom (.var 1) (.var 3)))
    (hg : PrfH Γ (isFC1 (.var 2) (.var 1) (.var 3))) :
    PrfH Γ (hasWitF (liftfc (.var 0) (.var 3))) := by
  have hshape := PrfH_and_elim_left hcl
  have hargs := PrfH_and_elim_right hcl
  have hwT := PrfH_and_elim_left (PrfH_and_elim_left hg)
  have hargsW := PrfH.mp _ _ _
    (prf_to_prfH (prf_hasWitArgs_liftsc_of (.var 1) (.var 0) BF) _)
    (PrfH_and_intro hwT hargs)
  have hnode := PrfH.mp _ _ _ (prf_to_prfH
    (prf_hasWitF_atomc AF (liftsc (.var 0) BF)) _) hargsW
  have h1 : PrfH Γ (liftfc (.var 0) (.var 3) =eq liftfc (.var 0) (atomc AF BF)) :=
    PrfH_congr_liftfc hshape
  have h2 : PrfH Γ (liftfc (.var 0) (atomc AF BF) =eq atomc AF (liftsc (.var 0) BF)) :=
    prf_to_prfH (prf_liftfc_atom (.var 0) AF BF) _
  exact PrfH_congr_hasWitF (PrfH_eq_symm (PrfH_eq_trans h1 h2)) hnode

private theorem casoF_eq {Γ : List Formula} (hcl : PrfH Γ (clEq (.var 1) (.var 3)))
    (hg : PrfH Γ (isFC1 (.var 2) (.var 1) (.var 3))) :
    PrfH Γ (hasWitF (liftfc (.var 0) (.var 3))) := by
  have hshape := PrfH_and_elim_left hcl
  have hins := PrfH_and_elim_right hcl
  have hinA := PrfH_and_elim_left hins
  have hinB := PrfH_and_elim_right hins
  have hwT := PrfH_and_elim_left (PrfH_and_elim_left hg)
  have hA := PrfH.mp _ _ _
    (prf_to_prfH (prf_hasWit_liftc_of_isTC1 (.var 1) (.var 0) AF) _)
    (PrfH_and_intro hwT hinA)
  have hB := PrfH.mp _ _ _
    (prf_to_prfH (prf_hasWit_liftc_of_isTC1 (.var 1) (.var 0) BF) _)
    (PrfH_and_intro hwT hinB)
  have hnode := PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (prf_hasWitF_eqc
    (liftc (.var 0) AF) (liftc (.var 0) BF)) _) hA) hB
  have h1 : PrfH Γ (liftfc (.var 0) (.var 3) =eq liftfc (.var 0) (eqc AF BF)) :=
    PrfH_congr_liftfc hshape
  have h2 : PrfH Γ (liftfc (.var 0) (eqc AF BF)
      =eq eqc (liftc (.var 0) AF) (liftc (.var 0) BF)) :=
    prf_to_prfH (prf_liftfc_eq (.var 0) AF BF) _
  exact PrfH_congr_hasWitF (PrfH_eq_symm (PrfH_eq_trans h1 h2)) hnode

private theorem casoF_bin {Γ : List Formula} (k : Nat)
    (inj : ∀ wF wT X : Term, Prf (Formula.impl (clBin wF X k) (isFormCodeE2 wF wT X)))
    (heqn : ∀ v a b : Term, Prf (liftfc v (binN k a b)
      =eq binN k (liftfc v a) (liftfc v b)))
    (hcl : PrfH Γ (clBin (.var 2) (.var 3) k))
    (hg : PrfH Γ (isFC1 (.var 2) (.var 1) (.var 3)))
    (hpsi : PrfH Γ (liftFormula 0 (liftFormula 0 (liftFormula 0 (PSI PHILF))))) :
    PrfH Γ (hasWitF (liftfc (.var 0) (.var 3))) := by
  have hshape := PrfH_and_elim_left hcl
  have hins := PrfH_and_elim_right hcl
  have hinA := PrfH_and_elim_left hins
  have hinB := PrfH_and_elim_right hins
  have hwT := PrfH_and_elim_left (PrfH_and_elim_left hg)
  have hwF := PrfH_and_elim_right (PrfH_and_elim_left hg)
  have cA1 : Prf (lt AF (cons AF (cons BF nil))) := prf_cantor_mono_left _ _
  have cA2 : Prf (lt (cons AF (cons BF nil)) (binN k AF BF)) := prf_cantor_mono_right _ _
  have cA : Prf (lt AF (binN k AF BF)) := prf_mp (prf_mp (prf_lt_trans _ _ _) cA1) cA2
  have cB1 : Prf (lt BF (cons BF nil)) := prf_cantor_mono_left _ _
  have cB2 : Prf (lt (cons BF nil) (cons AF (cons BF nil))) := prf_cantor_mono_right _ _
  have cB12 : Prf (lt BF (cons AF (cons BF nil))) :=
    prf_mp (prf_mp (prf_lt_trans _ _ _) cB1) cB2
  have cB : Prf (lt BF (binN k AF BF)) := prf_mp (prf_mp (prf_lt_trans _ _ _) cB12) cA2
  have hltA := PrfH_lt_subst2 (PrfH_eq_symm hshape) (prf_to_prfH cA _)
  have hltB := PrfH_lt_subst2 (PrfH_eq_symm hshape) (prf_to_prfH cB _)
  have hihA := PrfH.mp _ _ _ (PSI_inst3 PHILF hPHILF hpsi AF) hltA
  have hA := PrfH.mp _ _ _ (PHILF_use AF (.var 2) (.var 1) (.var 0) hihA)
    (PrfH_and_intro (PrfH_and_intro hwT hwF) hinA)
  have hihB := PrfH.mp _ _ _ (PSI_inst3 PHILF hPHILF hpsi BF) hltB
  have hB := PrfH.mp _ _ _ (PHILF_use BF (.var 2) (.var 1) (.var 0) hihB)
    (PrfH_and_intro (PrfH_and_intro hwT hwF) hinB)
  have hnode := PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (prf_hasWitF_bin k
    (liftfc (.var 0) AF) (liftfc (.var 0) BF) inj) _) hA) hB
  have h1 : PrfH Γ (liftfc (.var 0) (.var 3) =eq liftfc (.var 0) (binN k AF BF)) :=
    PrfH_congr_liftfc hshape
  have h2 : PrfH Γ (liftfc (.var 0) (binN k AF BF)
      =eq binN k (liftfc (.var 0) AF) (liftfc (.var 0) BF)) :=
    prf_to_prfH (heqn (.var 0) AF BF) _
  exact PrfH_congr_hasWitF (PrfH_eq_symm (PrfH_eq_trans h1 h2)) hnode

/-- **Los dos casos UNARIOS** (`forallc`/`exc`, tags 6/9). El binder SUBE el nivel: la HI se aplica
    con `σv`. ⭐ Y a diferencia del molde, **no hace falta levantar ningún testigo**: lo único que
    sube es el nivel, que no lleva guarda. Es la razón de que `v` viaje dentro de `Φ`. -/
private theorem casoF_un {Γ : List Formula} (k : Nat)
    (inj : ∀ wF wT X : Term, Prf (Formula.impl (clUn wF X k) (isFormCodeE2 wF wT X)))
    (heqn : ∀ v a : Term, Prf (liftfc v (unN k a) =eq unN k (liftfc (succ v) a)))
    (hcl : PrfH Γ (clUn (.var 2) (.var 3) k))
    (hg : PrfH Γ (isFC1 (.var 2) (.var 1) (.var 3)))
    (hpsi : PrfH Γ (liftFormula 0 (liftFormula 0 (liftFormula 0 (PSI PHILF))))) :
    PrfH Γ (hasWitF (liftfc (.var 0) (.var 3))) := by
  have hshape := PrfH_and_elim_left hcl
  have hinA := PrfH_and_elim_right hcl
  have hwT := PrfH_and_elim_left (PrfH_and_elim_left hg)
  have hwF := PrfH_and_elim_right (PrfH_and_elim_left hg)
  have cA1 : Prf (lt AF (cons AF nil)) := prf_cantor_mono_left _ _
  have cA2 : Prf (lt (cons AF nil) (unN k AF)) := prf_cantor_mono_right _ _
  have cA : Prf (lt AF (unN k AF)) := prf_mp (prf_mp (prf_lt_trans _ _ _) cA1) cA2
  have hltA := PrfH_lt_subst2 (PrfH_eq_symm hshape) (prf_to_prfH cA _)
  have hihA := PrfH.mp _ _ _ (PSI_inst3 PHILF hPHILF hpsi AF) hltA
  have hA := PrfH.mp _ _ _ (PHILF_use AF (.var 2) (.var 1) (succ (.var 0)) hihA)
    (PrfH_and_intro (PrfH_and_intro hwT hwF) hinA)
  have hnode := PrfH.mp _ _ _ (prf_to_prfH (prf_hasWitF_un k
    (liftfc (succ (.var 0)) AF) inj) _) hA
  have h1 : PrfH Γ (liftfc (.var 0) (.var 3) =eq liftfc (.var 0) (unN k AF)) :=
    PrfH_congr_liftfc hshape
  have h2 : PrfH Γ (liftfc (.var 0) (unN k AF) =eq unN k (liftfc (succ (.var 0)) AF)) :=
    prf_to_prfH (heqn (.var 0) AF) _
  exact PrfH_congr_hasWitF (PrfH_eq_symm (PrfH_eq_trans h1 h2)) hnode

/-! ## §9 · EL PASO ENSAMBLADO, y 🏁 LA CLAUSURA DE FÓRMULA -/

private def CTXF : List Formula :=
  [isFC1 (.var 2) (.var 1) (.var 3),
   liftFormula 0 (liftFormula 0 (liftFormula 0 (PSI PHILF)))]

theorem PHILF_step : Prf (Formula.forall (Formula.impl (PSI PHILF) PHILF)) := by
  refine Prf.gen _ (prf_deduction ?_)
  refine PrfH.gen [PSI PHILF] _ ?_
  simp only [List.map_cons, List.map_nil]
  refine PrfH.gen _ _ ?_
  simp only [List.map_cons, List.map_nil]
  refine PrfH.gen _ _ ?_
  simp only [List.map_cons, List.map_nil]
  refine deduction_aux ?_ (isFC1 (.var 2) (.var 1) (.var 3))
    [liftFormula 0 (liftFormula 0 (liftFormula 0 (PSI PHILF)))] rfl
  have hg : PrfH CTXF (isFC1 (.var 2) (.var 1) (.var 3)) := PrfH.hyp _ _ (List.Mem.head _)
  have hcode := PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH
      (prf_isFormCodeE2_of_In (.var 2) (.var 1) (.var 3)) _)
      (PrfH_and_elim_right hg))
    (PrfH_and_elim_right (PrfH_and_elim_left hg))
  refine PrfH_or_elim hcode (casoF_bot (PrfH.hyp _ _ (List.Mem.head _))) ?_
  refine PrfH_or_elim (PrfH.hyp _ _ (List.Mem.head _))
    (casoF_atom (PrfH.hyp _ _ (List.Mem.head _))
      (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))) ?_
  refine PrfH_or_elim (PrfH.hyp _ _ (List.Mem.head _))
    (casoF_eq (PrfH.hyp _ _ (List.Mem.head _))
      (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.head _)))))) ?_
  refine PrfH_or_elim (PrfH.hyp _ _ (List.Mem.head _))
    (casoF_bin 5 inj_bin5 (fun v a b => prf_liftfc_impl v a b)
      (PrfH.hyp _ _ (List.Mem.head _))
      (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.head _))))))
      (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))) ?_
  refine PrfH_or_elim (PrfH.hyp _ _ (List.Mem.head _))
    (casoF_un 6 inj_un6 (fun v a => prf_liftfc_forall v a)
      (PrfH.hyp _ _ (List.Mem.head _))
      (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
      (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))) ?_
  refine PrfH_or_elim (PrfH.hyp _ _ (List.Mem.head _))
    (casoF_bin 7 inj_bin7 (fun v a b => prf_liftfc_and v a b)
      (PrfH.hyp _ _ (List.Mem.head _))
      (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
      (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
          (List.Mem.tail _ (List.Mem.head _)))))))))) ?_
  refine PrfH_or_elim (PrfH.hyp _ _ (List.Mem.head _))
    (casoF_bin 8 inj_bin8 (fun v a b => prf_liftfc_or v a b)
      (PrfH.hyp _ _ (List.Mem.head _))
      (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
          (List.Mem.tail _ (List.Mem.head _)))))))))
      (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
          (List.Mem.tail _ (List.Mem.head _))))))))))) ?_
  exact casoF_un 9 inj_un9 (fun v a => prf_liftfc_ex v a)
    (PrfH.hyp _ _ (List.Mem.head _))
    (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.head _)))))))))
    (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.head _))))))))))

theorem PHILF_all (t : Term) : Prf (substFormula 0 t PHILF) :=
  prf_strong_induction PHILF hPHILF PHILF_step t

/-- **LA CLAUSURA DE FÓRMULA, con testigo EXPLÍCITO.** -/
theorem prf_hasWitF_liftfc_of_isFC1 (wF wT v X : Term) :
    Prf (Formula.impl (isFC1 wF wT X) (hasWitF (liftfc v X))) :=
  prfH_nil_to_prf (PHILF_use X wF wT v (prf_to_prfH (PHILF_all X) [])) rfl

/-- 🏁🏁 **LA CLAUSURA DEL TESTIGO BAJO `liftfc`**, con el código y el nivel ABSTRACTOS.
    Es la deuda `DEUDA_hasWitF_liftfc` de `Meta/EvalLiftfcPrf.lean` §12, saldada. -/
theorem prf_hasWitF_liftfc (v X : Term) :
    Prf (Formula.impl (hasWitF X) (hasWitF (liftfc v X))) := by
  refine prf_ex_elim_imp ?_
  refine PrfH_ex_elim (PrfH.hyp _ _ (List.Mem.head _)) ?_
  simp only [List.map_cons, List.map_nil]
  have hg : liftFormula 0 (liftFormula 0 (hasWitF (liftfc v X)))
      = hasWitF (liftfc (liftTerm 0 (liftTerm 0 v)) (liftTerm 0 (liftTerm 0 X))) := by
    simp only [liftF_hasWitF, liftfc, liftTerm, liftTerms]
  rw [hg]
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_hasWitF_liftfc_of_isFC1 (.var 1) (.var 0)
    (liftTerm 0 (liftTerm 0 v)) (liftTerm 0 (liftTerm 0 X))) _)
    (PrfH.hyp _ _ (List.Mem.head _))

/-- 🏁 **LA DEUDA, SALDADA.** -/
theorem deuda_hasWitF_liftfc : DEUDA_hasWitF_liftfc := prf_hasWitF_liftfc

/-- La forma de APLICACIÓN. -/
theorem prf_hasWitF_liftfc_mp (v X : Term) (hX : Prf (hasWitF X)) :
    Prf (hasWitF (liftfc v X)) := prf_mp (prf_hasWitF_liftfc v X) hX


end ROBINSON_PlusPlus.Meta.LiftfcWitnessPrf

/-! ## `export` — por CONSUMO (AI-GUIDE §17)

Los consumidores previstos son **`Meta/SubstTreeReflect.lean`** (los reflectores `ind` y
`listInd`, que piden `hasWitF (liftfc k A)`) y, a través de ellos, `pcc_lineWF_tracked` y el
`hbody`(a) de D3. Las piezas de armazón (`PHIL*`, `BODY*`, los `spec`) quedan **fuera**: son
internas de la inducción y nadie las consume desde fuera. -/
export ROBINSON_PlusPlus.Meta.LiftfcWitnessPrf (
  PrfH_congr_liftsc PrfH_congr_liftfc
  prf_hasWit_liftc_of_isTC1 prf_hasWit_liftc_at prf_hasWitArgs_liftsc_of
  prf_hasWitF_liftfc_of_isFC1 prf_hasWitF_liftfc prf_hasWitF_liftfc_mp
  deuda_hasWitF_liftfc
)

/-! ## FOOTPRINT -/

#print axioms ROBINSON_PlusPlus.Meta.LiftfcWitnessPrf.prf_hasWit_liftc_at
#print axioms ROBINSON_PlusPlus.Meta.LiftfcWitnessPrf.prf_hasWitArgs_liftsc_of
#print axioms ROBINSON_PlusPlus.Meta.LiftfcWitnessPrf.prf_hasWitF_liftfc
#print axioms ROBINSON_PlusPlus.Meta.LiftfcWitnessPrf.deuda_hasWitF_liftfc

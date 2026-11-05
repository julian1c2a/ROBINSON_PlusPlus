/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import FOL.Lift0
import FOL.Theorems.Quantifiers
import ROBINSON_PlusPlus.Minimal.Axioms
import ROBINSON_PlusPlus.Meta.Hilbert
import ROBINSON_PlusPlus.Meta.HilbertDeduction
import ROBINSON_PlusPlus.Meta.ReprPrf
import ROBINSON_PlusPlus.Meta.ArithPrf
import ROBINSON_PlusPlus.Meta.ChainPrf
import ROBINSON_PlusPlus.Meta.NatArithPrf
import ROBINSON_PlusPlus.Meta.NatOrderPrf
import ROBINSON_PlusPlus.Meta.NatMulPrf
import ROBINSON_PlusPlus.Meta.CantorMonoPrf
import ROBINSON_PlusPlus.Meta.StrongInductionPrf
import ROBINSON_PlusPlus.Meta.Div2ParityPrf
import ROBINSON_PlusPlus.Meta.CodeWitnessPrf

/-!
# `Meta/ListIndAdmisible.lean` — la inducción de LISTAS es ADMISIBLE en `Prf`: sale de la ordinaria, sin `listInd`

🏁 **`listInd_admisible (A : Formula) : Prf (listInductionFormula A)`**, para TODA `A` (con parámetros), sin el
constructor `Prf.listInd`, ni directamente ni por ningún lema que use. Footprint: `[propext, Quot.sound]`. Corolario:
`prf_list_induction_sin`, la regla derivada de `Meta/ChainPrf.lean` (`prf_list_induction`) con la misma firma y sin
`listInd`.

**De dónde viene:** de `sondeos/ListIndAdmisible.lean` (T69, ADR‑244: Gentzen, los primeros pasos medibles), que la
demostró el 2026‑11‑02; ADR‑259 la sube al build tal cual, §1–§5, y deja en el sondeo la MEDIDA —qué reglas de
inducción construye la prueba: ningún paso `listInd` ni `p3` fuera de las traducciones— con sus controles positivos.

**Cómo** (la ruta natural: inducción fuerte sobre el CÓDIGO; `L = nil`, o `L = cons h t` con `t < L`):
* §1 · De Bruijn: dos instancias de `FOL.Lift0.liftFormula_subst`, un alias y un corolario.
* §2 · Inducción fuerte para TODA `Φ`: `prf_strong_ind_formula Φ : Prf (∀(PSI Φ ⇒ Φ) ⇒ ∀Φ)`; la de
  `Meta/StrongInductionPrf.lean` pide `liftFormula 1 Φ = Φ`, y una instancia de `listInductionFormula` puede tener
  parámetros.
* §3 · Cantor: `σ(pair (σh) t) = pair h (σt)`, `σ(pair 0 t) = pair (σt) 0` y `pair 0 0 = 0`.
* §4 · Todo código no nulo es un `cons`: `prf_nil_or_consOk`, por `ind` sobre una ECUACIÓN (el de
  `Meta/SubstfcWitnessPrf.lean`, `prf_nil_or_cons`, sale de `listInd`).
* §5 · El ensamblaje: la inducción fuerte de §2 sobre el código, con la cola menor por `prf_cantor_mono_right`.

**Lo que NO dice:** que `listInd` sobre en el CÓDIGO. El constructor sigue en `Prf`, `PrfH` y el verificador
(`HilbertSeq.Rule.listInd`, `ax_lineWF_listInd`), y `AxiomasT` (`Meta/PuenteFOL.lean`) lo lleva; quitarlo cambiaría
la teoría codificada, el ancla y `G` (L5‑04, ADR‑254: la tabla de reglas, sólo si cambian las reglas). Lo que dice es
que como TEORÍA no añade nada. Y los usuarios de `prf_list_induction` (D2 entre ellos) siguen usándola: redirigirlos a
`prf_list_induction_sin` es otro paso, que cambiaría lo que usa la prueba de un titular.
-/

open FOL
open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.NatArithPrf
open ROBINSON_PlusPlus.Meta.NatOrderPrf
open ROBINSON_PlusPlus.Meta.NatMulPrf
open ROBINSON_PlusPlus.Meta.CantorMonoPrf
open ROBINSON_PlusPlus.Meta.StrongInductionPrf
open ROBINSON_PlusPlus.Meta.Div2ParityPrf

namespace ROBINSON_PlusPlus.Meta.ListIndAdmisible

/-! ## §1 · De Bruijn: dos instancias de `FOL.Lift0.liftFormula_subst` y un corolario -/

theorem lift0_subst0 (Y : Formula) (s : Term) :
    liftFormula 0 (substFormula 0 s Y) = substFormula 0 (liftTerm 0 s) (liftFormula 1 Y) :=
  FOL.Lift0.liftFormula_subst Y 0 0 (Nat.le_refl 0) s

theorem lift2_subst0 (Y : Formula) (s : Term) :
    liftFormula 2 (substFormula 0 s Y) = substFormula 0 (liftTerm 2 s) (liftFormula 3 Y) :=
  FOL.Lift0.liftFormula_subst Y 0 2 (Nat.zero_le 2) s

/-- `Φ(#0)` deshace el `lift 1`: alias de `subst_lift_cancel_formula` en `v = 0`. -/
theorem subst0_lift1 (X : Formula) : substFormula 0 (.var 0) (liftFormula 1 X) = X :=
  FOL.Theorems.Quantifiers.subst_lift_cancel_formula X 0

/-- `Φ(#1)` con los parámetros subidos dos veces es `↑Φ`. -/
theorem subst1_lift11 (X : Formula) :
    substFormula 0 (.var 1) (liftFormula 1 (liftFormula 1 X)) = liftFormula 0 X := by
  have h := lift0_subst0 (liftFormula 1 X) (.var 0)
  rw [subst0_lift1 X] at h
  rw [h]
  simp [liftTerm]

/-! ## §2 · Inducción FUERTE para TODA `Φ`, con parámetros

`prf_strong_induction` (`Meta/StrongInductionPrf.lean`) pide `liftFormula 1 Φ = Φ`: sin más libres que
`#0`. Una instancia de `listInductionFormula` puede tener parámetros. Aquí, la misma prueba (inducción
ordinaria sobre `PSI Φ`) sin esa hipótesis, como FÓRMULA: `∀(PSI Φ ⇒ Φ) ⇒ ∀Φ`. -/

/-- La base: `PSI Φ (0)` es vacía. -/
theorem prf_psi_zero (Φ : Formula) : Prf (substFormula 0 zero (PSI Φ)) := by
  rw [psi_at]
  refine Prf.gen _ (prf_deduction ?_)
  have hlt0 : PrfH [lt (.var 0) (liftTerm 0 zero)] (lt (.var 0) zero) := by
    simpa only [liftTerm, liftTerms, zero] using prfH_hyp_self (lt (.var 0) (liftTerm 0 zero))
  exact PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prfᵢ.efq Φ))
    (PrfH.mp _ _ _ (prf_to_prfH (prf_not_lt_zero (.var 0)) _) hlt0)

/-- `liftFormula 0 (PSI Φ)`, sin pedir nada a `Φ`. -/
theorem lift0_PSI (Φ : Formula) :
    liftFormula 0 (PSI Φ)
      = Formula.forall (Formula.impl (lt (.var 0) (.var 2)) (liftFormula 1 (liftFormula 1 Φ))) := by
  simp only [PSI, liftFormula, lt, liftTerms, liftTerm, Nat.reduceAdd, Nat.reduceLT, reduceIte]

/-- `∀n PSI Φ(n) ⇒ ∀n Φ(n)`. -/
theorem prf_allPSI_imp_all (Φ : Formula) :
    Prf (Formula.forall (PSI Φ) ⇒ Formula.forall Φ) := by
  refine prf_deduction ?_
  refine PrfH.gen _ _ ?_
  show PrfH [liftFormula 0 (Formula.forall (PSI Φ))] Φ
  have h1 : PrfH [liftFormula 0 (Formula.forall (PSI Φ))]
      (Formula.forall (liftFormula 1 (PSI Φ))) := prfH_hyp_self _
  have h2 := PrfH_spec h1 (succ (.var 0))
  rw [psi_step_motive] at h2
  have h3 := PrfH_spec h2 (.var 0)
  have e : substFormula 0 (.var 0)
      (Formula.impl (lt (.var 0) (succ (.var 1))) (liftFormula 1 Φ))
      = Formula.impl (lt (.var 0) (succ (.var 0))) Φ := by
    simp only [substFormula, lt, succ, substTerms, substTerm, Nat.reduceEqDiff, Nat.reduceGT,
      Nat.reduceSub, reduceIte, ite_true, subst0_lift1]
  rw [e] at h3
  exact PrfH.mp _ _ _ h3 (prf_to_prfH (prf_lt_succ_self_cm (.var 0)) _)

/-- ⭐ **Inducción fuerte como fórmula, para TODA `Φ`**: `∀(PSI Φ ⇒ Φ) ⇒ ∀Φ`. Sólo `ind`
    (el constructor `PrfH.ind`) y lógica. -/
theorem prf_strong_ind_formula (Φ : Formula) :
    Prf (Formula.forall (Formula.impl (PSI Φ) Φ) ⇒ Formula.forall Φ) := by
  refine prf_deduction ?_
  have hall : PrfH [Formula.forall (Formula.impl (PSI Φ) Φ)] (Formula.forall (PSI Φ)) := by
    refine PrfH.mp _ _ _ (PrfH.mp _ _ _ (PrfH.ind _ (PSI Φ)) ?base) ?step
    · exact prf_to_prfH (prf_psi_zero Φ) _
    · refine PrfH.gen _ _ ?_
      show PrfH [liftFormula 0 (Formula.forall (Formula.impl (PSI Φ) Φ))]
        (Formula.impl (PSI Φ) (substFormula 0 (succ (.var 0)) (liftFormula 1 (PSI Φ))))
      rw [psi_step_motive]
      refine deduction_aux ?_ (PSI Φ) _ rfl
      refine PrfH.gen _ _ ?_
      show PrfH [liftFormula 0 (PSI Φ),
          liftFormula 0 (liftFormula 0 (Formula.forall (Formula.impl (PSI Φ) Φ)))]
        (Formula.impl (lt (.var 0) (succ (.var 1))) (liftFormula 1 Φ))
      refine deduction_aux ?_ (lt (.var 0) (succ (.var 1))) _ rfl
      have hsplit : PrfH [lt (.var 0) (succ (.var 1)), liftFormula 0 (PSI Φ),
          liftFormula 0 (liftFormula 0 (Formula.forall (Formula.impl (PSI Φ) Φ)))]
          (lor (lt (.var 0) (.var 1)) ((.var 0) =eq (.var 1))) :=
        PrfH.mp _ _ _ (prf_to_prfH (prf_le_of_lt_succ (.var 0) (.var 1)) _)
          (PrfH.hyp _ _ (List.Mem.head _))
      refine PrfH_or_elim hsplit ?brA ?brB
      case brA =>
        -- `m < n`: la hipótesis de curso de valores, en `m`
        -- (el contexto, con `let`: un `rw … at` no debe tocar las hipótesis de la lista)
        let Γ : List Formula := lt (.var 0) (.var 1) :: lt (.var 0) (succ (.var 1)) ::
          liftFormula 0 (PSI Φ) ::
          [liftFormula 0 (liftFormula 0 (Formula.forall (Formula.impl (PSI Φ) Φ)))]
        have hpsi : PrfH Γ (liftFormula 0 (PSI Φ)) :=
          PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
        rw [lift0_PSI] at hpsi
        have h := PrfH_spec hpsi (.var 0)
        have e : substFormula 0 (.var 0)
            (Formula.impl (lt (.var 0) (.var 2)) (liftFormula 1 (liftFormula 1 Φ)))
            = Formula.impl (lt (.var 0) (.var 1)) (liftFormula 1 Φ) := by
          simp only [substFormula, lt, substTerms, substTerm, Nat.reduceEqDiff, Nat.reduceGT,
            Nat.reduceSub, reduceIte, ite_true, subst0_lift1]
        rw [e] at h
        exact PrfH.mp _ _ _ h (PrfH.hyp _ _ (List.Mem.head _))
      case brB =>
        -- `m = n`: el paso en `n`, y Leibniz de `n` a `m`
        let Γ : List Formula := (Formula.eq (.var 0) (.var 1)) :: lt (.var 0) (succ (.var 1)) ::
          liftFormula 0 (PSI Φ) ::
          [liftFormula 0 (liftFormula 0 (Formula.forall (Formula.impl (PSI Φ) Φ)))]
        have hpsi : PrfH Γ (liftFormula 0 (PSI Φ)) :=
          PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
        have hH : PrfH Γ (Formula.forall (Formula.impl
            (liftFormula 1 (liftFormula 1 (PSI Φ))) (liftFormula 1 (liftFormula 1 Φ)))) :=
          PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
        have h := PrfH_spec hH (.var 1)
        have e : substFormula 0 (.var 1) (Formula.impl
            (liftFormula 1 (liftFormula 1 (PSI Φ))) (liftFormula 1 (liftFormula 1 Φ)))
            = Formula.impl (liftFormula 0 (PSI Φ))
                (substFormula 0 (.var 1) (liftFormula 1 (liftFormula 1 Φ))) := by
          simp only [substFormula]
          rw [subst1_lift11]
        rw [e] at h
        have hR := PrfH.mp _ _ _ h hpsi
        have hsym : PrfH Γ ((.var 1 : Term) =eq (.var 0)) :=
          PrfH_eq_symm (PrfH.hyp _ _ (List.Mem.head _))
        have hg := PrfH_leibniz_subst (A := liftFormula 1 (liftFormula 1 Φ)) hsym hR
        rw [subst0_lift1] at hg
        exact hg
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_allPSI_imp_all Φ) _) hall

/-! ## §3 · Aritmética de Cantor: `σ(pair h t)` es otro `pair`

`pair h t` es, por definición, `div2 (cpOf h t)`, y `prf_pair_double` (`Meta/Div2ParityPrf.lean`) da
`(div2 (cpOf h t))·2 = cpOf h t`. Las dos identidades de la sobreyectividad, por el camino de Cantor:
`σ(pair (σh) t) = pair h (σt)` (se baja por la diagonal) y `σ(pair 0 t) = pair (σt) 0` (se salta a la
siguiente). En las dos, el polinomio de llegada es el de salida más `2`, y `prf_div2_double` lo parte. -/

/-- `(σP)·2 = P·2 + 2`. -/
theorem prf_succ_mul_two (P : Term) : Prf (mul (succ P) two =eq add (mul P two) two) :=
  prf_eq_trans (prf_mul_comm (succ P) two)
    (prf_eq_trans (prf_mul_succ two P) (prf_eq_congr_add1 two (prf_mul_comm two P)))

/-- Si el polinomio de llegada es el de salida más `2`, su mitad es el sucesor de la de salida. -/
theorem prf_div2_add_two {X : Term} (h t : Term) (hX : Prf (X =eq add (cpOf h t) two)) :
    Prf (div2 X =eq succ (div2 (cpOf h t))) := by
  have e2 : Prf (add (cpOf h t) two =eq mul (succ (div2 (cpOf h t))) two) :=
    prf_eq_trans (prf_eq_congr_add1 two (prf_eq_symm (prf_pair_double h t)))
      (prf_eq_symm (prf_succ_mul_two (div2 (cpOf h t))))
  exact prf_eq_trans (prf_eq_congr_div2 (prf_eq_trans hX e2))
    (prf_div2_double (succ (div2 (cpOf h t))))

/-- `x·σx` es congruente en `x`. -/
theorem prf_congr_mul_succ_self {a b : Term} (h : Prf (a =eq b)) :
    Prf (mul a (succ a) =eq mul b (succ b)) :=
  prf_eq_trans (prf_eq_congr_mul1 (succ a) h) (prf_eq_congr_mul2 b (prf_eq_congr_succ h))

/-- **`cpOf h (σt) = cpOf (σh) t + 2`**: misma diagonal `s = σ(h+t)`, y `2·σt = 2·t + 2`. -/
theorem prf_cpOf_shift (h t : Term) : Prf (cpOf h (succ t) =eq add (cpOf (succ h) t) two) := by
  have q1 : Prf (mul (add h (succ t)) (succ (add h (succ t)))
      =eq mul (succ (add h t)) (succ (succ (add h t)))) :=
    prf_congr_mul_succ_self (prf_add_succ_t h t)
  have q2 : Prf (mul (add (succ h) t) (succ (add (succ h) t))
      =eq mul (succ (add h t)) (succ (succ (add h t)))) :=
    prf_congr_mul_succ_self (prf_add_succ_left h t)
  have s1 : Prf (cpOf h (succ t)
      =eq add (mul (succ (add h t)) (succ (succ (add h t)))) (add (mul two t) two)) :=
    prf_eq_trans (prf_eq_congr_add1 (mul two (succ t)) q1)
      (prf_eq_congr_add2 (mul (succ (add h t)) (succ (succ (add h t)))) (prf_mul_succ two t))
  have s2 : Prf (add (mul (succ (add h t)) (succ (succ (add h t)))) (add (mul two t) two)
      =eq add (add (mul (succ (add h t)) (succ (succ (add h t)))) (mul two t)) two) :=
    prf_eq_symm (prf_add_assoc (mul (succ (add h t)) (succ (succ (add h t)))) (mul two t) two)
  have s3 : Prf (add (add (mul (succ (add h t)) (succ (succ (add h t)))) (mul two t)) two
      =eq add (cpOf (succ h) t) two) :=
    prf_eq_congr_add1 two (prf_eq_congr_add1 (mul two t) (prf_eq_symm q2))
  exact prf_eq_trans s1 (prf_eq_trans s2 s3)

/-- **`σ(pair (σh) t) = pair h (σt)`**. -/
theorem prf_pair_shift (h t : Term) :
    Prf (succ (div2 (cpOf (succ h) t)) =eq div2 (cpOf h (succ t))) :=
  prf_eq_symm (prf_div2_add_two (succ h) t (prf_cpOf_shift h t))

/-- **`cpOf (σt) 0 = cpOf 0 t + 2`**: `σt·σσt = t·σt + (σt + σt)` por los dos lados. -/
theorem prf_cpOf_wrap (t : Term) : Prf (cpOf (succ t) zero =eq add (cpOf zero t) two) := by
  -- lado izquierdo: `cpOf (σt) 0 = σt·σσt = t·σt + (σt + σt)`
  have l1 : Prf (cpOf (succ t) zero =eq mul (succ t) (succ (succ t))) :=
    prf_eq_trans
      (prf_eq_trans (prf_eq_congr_add1 (mul two zero)
          (prf_congr_mul_succ_self (prf_add_zero_t (succ t))))
        (prf_eq_congr_add2 (mul (succ t) (succ (succ t))) (prf_mul_zero two)))
      (prf_add_zero_t (mul (succ t) (succ (succ t))))
  have l2 : Prf (mul (succ t) (succ (succ t))
      =eq add (mul t (succ t)) (add (succ t) (succ t))) :=
    prf_eq_trans (prf_mul_succ (succ t) (succ t))
      (prf_eq_trans (prf_eq_congr_add1 (succ t)
          (prf_eq_trans (prf_mul_succ (succ t) t)
            (prf_eq_congr_add1 (succ t) (prf_mul_comm (succ t) t))))
        (prf_add_assoc (mul t (succ t)) (succ t) (succ t)))
  -- lado derecho: `cpOf 0 t + 2 = (t·σt + 2·t) + 2 = t·σt + 2·σt = t·σt + (σt + σt)`
  have r1 : Prf (add (cpOf zero t) two =eq add (add (mul t (succ t)) (mul two t)) two) :=
    prf_eq_congr_add1 two (prf_eq_congr_add1 (mul two t)
      (prf_congr_mul_succ_self (prf_add_zero_left t)))
  have r2 : Prf (add (add (mul t (succ t)) (mul two t)) two
      =eq add (mul t (succ t)) (add (succ t) (succ t))) :=
    prf_eq_trans (prf_add_assoc (mul t (succ t)) (mul two t) two)
      (prf_eq_congr_add2 (mul t (succ t))
        (prf_eq_trans (prf_eq_symm (prf_mul_succ two t))
          (prf_eq_trans (prf_mul_comm two (succ t)) (prf_mul_two (succ t)))))
  exact prf_eq_trans (prf_eq_trans l1 l2) (prf_eq_symm (prf_eq_trans r1 r2))

/-- **`σ(pair 0 t) = pair (σt) 0`**. -/
theorem prf_pair_wrap (t : Term) :
    Prf (succ (div2 (cpOf zero t)) =eq div2 (cpOf (succ t) zero)) :=
  prf_eq_symm (prf_div2_add_two zero t (prf_cpOf_wrap t))

/-- **`pair 0 0 = 0`**, luego `cons 0 0 = σ0`. -/
theorem prf_pair_zero : Prf (div2 (cpOf zero zero) =eq zero) := by
  have d2 : Prf (mul (add zero zero) (succ (add zero zero)) =eq zero) :=
    prf_eq_trans (prf_eq_congr_mul1 (succ (add zero zero)) (prf_add_zero_t zero))
      (prf_zero_mul (succ (add zero zero)))
  have hcp : Prf (cpOf zero zero =eq zero) :=
    prf_eq_trans
      (prf_eq_trans (prf_eq_congr_add1 (mul two zero) d2)
        (prf_eq_congr_add2 zero (prf_mul_zero two)))
      (prf_add_zero_t zero)
  exact prf_eq_trans (prf_eq_congr_div2 (prf_eq_trans hcp (prf_eq_symm (prf_zero_mul two))))
    (prf_div2_double zero)

/-! ## §4 · Todo código no nulo es un `cons`, SIN `listInd`

`prf_nil_or_cons` (`Meta/SubstfcWitnessPrf.lean`) lo saca de `prf_list_induction`, es decir, de
`Prf.listInd`. Aquí sale de `ind`: por inducción ordinaria sobre `c`, `consOk (σc)`
(`σc = cons (carc σc) (cdrc σc)`, sin `∃`), con el caso `carc σc = 0 ∨ = σ(pred ·)`. -/

/-- `consOk #0` con `#0` sustituido. -/
theorem consOk_at (s : Term) : substFormula 0 s (consOk (.var 0)) = consOk s := by
  simp only [consOk, carc, cdrc, cons, substFormula, substTerm, substTerms, ite_true]

/-- De `X = cons a b`, `consOk X`. -/
theorem PrfH_consOk_of_eq {Γ : List Formula} {X a b : Term} (h : PrfH Γ (X =eq cons a b)) :
    PrfH Γ (consOk X) :=
  (consOk_at X) ▸ PrfH_leibniz_subst (A := consOk (.var 0)) (PrfH_eq_symm h)
    ((consOk_at (cons a b)) ▸ prf_to_prfH (prf_consOk_cons a b) Γ)

/-- El paso: `consOk (σc) ⇒ consOk (σσc)`. -/
theorem prf_consOk_step (c : Term) : Prf (consOk (succ c) ⇒ consOk (succ (succ c))) := by
  refine prf_deduction ?_
  have hyp : PrfH [consOk (succ c)] (succ c =eq cons (carc (succ c)) (cdrc (succ c))) :=
    prfH_hyp_self _
  refine PrfH_or_elim (prf_to_prfH (prf_zero_or_eq_succ_pred (carc (succ c))) _) ?_ ?_
  · -- `carc σc = 0`: `σσc = cons (σ(cdrc σc)) 0`
    have h1 : PrfH [Formula.eq (carc (succ c)) zero, consOk (succ c)]
        (succ c =eq cons zero (cdrc (succ c))) :=
      PrfH_eq_trans (PrfH_w1 hyp) (PrfH_congr_cons_head (PrfH.hyp _ _ (List.Mem.head _)))
    have h2 : PrfH [Formula.eq (carc (succ c)) zero, consOk (succ c)]
        (succ c =eq succ (div2 (cpOf zero (cdrc (succ c))))) :=
      PrfH_eq_trans h1 (prf_to_prfH (prf_cons_div2 zero (cdrc (succ c))) _)
    have h3 : PrfH [Formula.eq (carc (succ c)) zero, consOk (succ c)]
        (c =eq div2 (cpOf zero (cdrc (succ c)))) :=
      PrfH.mp _ _ _ (prf_to_prfH (prf_succ_inj _ _) _) h2
    have h4 : PrfH [Formula.eq (carc (succ c)) zero, consOk (succ c)]
        (succ (succ c) =eq cons (succ (cdrc (succ c))) zero) :=
      PrfH_eq_trans (PrfH_eq_congr_succ (PrfH_eq_congr_succ h3))
        (prf_to_prfH (prf_eq_trans (prf_eq_congr_succ (prf_pair_wrap (cdrc (succ c))))
          (prf_eq_symm (prf_cons_div2 (succ (cdrc (succ c))) zero))) _)
    exact PrfH_consOk_of_eq h4
  · -- `carc σc = σp`: `σσc = cons p (σ(cdrc σc))`, con `p = pred (carc σc)`
    have h1 : PrfH [Formula.eq (carc (succ c)) (succ (pred (carc (succ c)))), consOk (succ c)]
        (succ c =eq cons (succ (pred (carc (succ c)))) (cdrc (succ c))) :=
      PrfH_eq_trans (PrfH_w1 hyp) (PrfH_congr_cons_head (PrfH.hyp _ _ (List.Mem.head _)))
    have h2 : PrfH [Formula.eq (carc (succ c)) (succ (pred (carc (succ c)))), consOk (succ c)]
        (succ c =eq succ (div2 (cpOf (succ (pred (carc (succ c)))) (cdrc (succ c))))) :=
      PrfH_eq_trans h1 (prf_to_prfH (prf_cons_div2 (succ (pred (carc (succ c)))) (cdrc (succ c))) _)
    have h3 : PrfH [Formula.eq (carc (succ c)) (succ (pred (carc (succ c)))), consOk (succ c)]
        (c =eq div2 (cpOf (succ (pred (carc (succ c)))) (cdrc (succ c)))) :=
      PrfH.mp _ _ _ (prf_to_prfH (prf_succ_inj _ _) _) h2
    have h4 : PrfH [Formula.eq (carc (succ c)) (succ (pred (carc (succ c)))), consOk (succ c)]
        (succ (succ c) =eq cons (pred (carc (succ c))) (succ (cdrc (succ c)))) :=
      PrfH_eq_trans (PrfH_eq_congr_succ (PrfH_eq_congr_succ h3))
        (prf_to_prfH (prf_eq_trans
          (prf_eq_congr_succ (prf_pair_shift (pred (carc (succ c))) (cdrc (succ c))))
          (prf_eq_symm (prf_cons_div2 (pred (carc (succ c))) (succ (cdrc (succ c)))))) _)
    exact PrfH_consOk_of_eq h4

/-- `consOk (σ#0)` con `#0` sustituido. -/
theorem consOk_succ_at (s : Term) :
    substFormula 0 s (consOk (succ (.var 0))) = consOk (succ s) := by
  simp only [consOk, carc, cdrc, cons, succ, substFormula, substTerm, substTerms, ite_true]

/-- ⭐ **`∀c consOk (σc)`**, por inducción ORDINARIA (`prf_nat_induction`, `Prf.ind`) sobre una ECUACIÓN. -/
theorem prf_consOk_succ_all : Prf (Formula.forall (consOk (succ (.var 0)))) := by
  refine prf_nat_induction _ ?base ?step
  · rw [consOk_succ_at]
    exact prfH_nil_to_prf (PrfH_consOk_of_eq (a := zero) (b := zero)
      (prf_to_prfH (prf_eq_symm (prf_eq_trans (prf_cons_div2 zero zero)
        (prf_eq_congr_succ prf_pair_zero))) [])) rfl
  · refine Prf.gen _ ?_
    have e : substFormula 0 (succ (.var 0)) (liftFormula 1 (consOk (succ (.var 0))))
        = consOk (succ (succ (.var 0))) := by
      simp only [consOk, carc, cdrc, cons, succ, liftFormula, liftTerm, liftTerms, substFormula,
        substTerm, substTerms, Nat.reduceLT, ite_true]
    rw [e]
    exact prf_consOk_step (.var 0)

theorem prf_consOk_succ (c : Term) : Prf (consOk (succ c)) := by
  have h := prf_spec prf_consOk_succ_all c
  rwa [consOk_succ_at] at h

/-- ⭐ **`L = nil ∨ consOk L`, SIN `listInd`** (frente a `prf_nil_or_cons`, que usa `listInd`). -/
theorem prf_nil_or_consOk (L : Term) : Prf (lor (L =eq nil) (consOk L)) := by
  refine prf_or_elim (prf_zero_or_eq_succ_pred L) (Prf.incl (Prfᵢ.j1 _ _)) ?_
  refine prf_deduction ?_
  have h := PrfH_leibniz_subst (A := consOk (.var 0))
    (PrfH_eq_symm (prfH_hyp_self (Formula.eq L (succ (pred L)))))
    ((consOk_at (succ (pred L))) ▸ prf_to_prfH (prf_consOk_succ (pred L)) _)
  rw [consOk_at] at h
  exact PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prfᵢ.j2 _ _)) h

/-! ## §5 · El ensamblaje: `listInductionFormula A` para TODA `A`, sin `listInd`

Con `B := A[nil]` y `S := ∀h∀t (A[t] ⇒ A[cons h t])` en contexto, la inducción fuerte de §2 sobre `A`
pide `∀n (PSI A(n) ⇒ A(n))`: por §4, `n = nil` (y `B`) o `n = cons (carc n) (cdrc n)`; la cola es menor
(`prf_cantor_mono_right`), `PSI` da `A(cola)` y `S` da `A(n)`. Lo único que exige cuidado es De Bruijn:
la instancia de `↑S` en `carc #0`, `cdrc #0` (`S_inst`). -/

theorem lift21 (A : Formula) : liftFormula 2 (liftFormula 1 A) = liftFormula 1 (liftFormula 1 A) :=
  liftFormula_swap A 1

theorem lift32 (A : Formula) : liftFormula 3 (liftFormula 2 A) = liftFormula 2 (liftFormula 2 A) :=
  liftFormula_swap A 2

/-- La instancia de `↑S` en `h`, `t`: `A[t] ⇒ A[cons h t]`, con `A[u] = substFormula 0 u (liftFormula 1 A)`
    (los parámetros de `A` donde deben estar bajo el `∀n` de la inducción). -/
theorem S_inst (A : Formula) (h t : Term) :
    substFormula 0 t (substFormula 1 (liftTerm 0 h) (liftFormula 2 (Formula.impl (liftFormula 1 A)
      (substFormula 0 (cons (.var 1) (.var 0)) (liftFormula 2 (liftFormula 1 A))))))
    = Formula.impl (substFormula 0 t (liftFormula 1 A)) (substFormula 0 (cons h t) (liftFormula 1 A)) := by
  simp only [liftFormula, substFormula]
  -- el antecedente
  rw [lift21, FOL.substFormula_liftFormula (liftFormula 1 A) 1 (liftTerm 0 h)]
  -- el consecuente
  rw [lift2_subst0]
  have hc2 : liftTerm 2 (cons (.var 1) (.var 0)) = cons (.var 1) (.var 0) := by
    simp [cons, liftTerm, liftTerms]
  rw [hc2]
  have hbar := FOL.subst_subst_comm_succ (liftFormula 3 (liftFormula 1 (liftFormula 1 A)))
    (liftTerm 0 h) (cons (.var 1) (.var 0)) 0
  simp only [Nat.zero_add] at hbar
  rw [hbar]
  have hc1 : substTerm 1 (liftTerm 0 h) (cons (.var 1) (.var 0)) = cons (liftTerm 0 h) (.var 0) := by
    simp [cons, substTerm, substTerms]
  rw [hc1]
  have h32 : liftFormula 3 (liftFormula 1 (liftFormula 1 A))
      = liftFormula 2 (liftFormula 1 (liftFormula 1 A)) := by
    rw [← lift21, lift32]
  rw [h32, FOL.substFormula_liftFormula (liftFormula 1 (liftFormula 1 A)) 2]
  have hsl := FOL.subst_subst_lift_gen (liftFormula 1 A) t (cons (liftTerm 0 h) (.var 0)) 0
  simp only [Nat.zero_add] at hsl
  rw [hsl]
  have hc0 : substTerm 0 t (cons (liftTerm 0 h) (.var 0)) = cons h t := by
    simp [cons, substTerm, substTerms, FOL.substTerm_liftTerm]
  rw [hc0]

/-- ⭐⭐ **LA INDUCCIÓN DE LISTAS, DERIVADA**: para toda `A`, `Prf (listInductionFormula A)` sin el
    constructor `Prf.listInd` (medido en §6: `#induccion` y `#induccionSin`). -/
theorem listInd_admisible (A : Formula) : Prf (listInductionFormula A) := by
  -- el contexto: `S` (el paso) y `B = A[nil]`
  have hgoal : PrfH [Formula.forall (Formula.forall (Formula.impl (liftFormula 1 A)
        (substFormula 0 (cons (.var 1) (.var 0)) (liftFormula 2 (liftFormula 1 A))))),
      substFormula 0 nil A] (Formula.forall A) := by
    refine PrfH.mp _ _ _ (prf_to_prfH (prf_strong_ind_formula A) _) ?_
    refine PrfH.gen _ _ ?_
    show PrfH [liftFormula 0 (Formula.forall (Formula.forall (Formula.impl (liftFormula 1 A)
        (substFormula 0 (cons (.var 1) (.var 0)) (liftFormula 2 (liftFormula 1 A)))))),
      liftFormula 0 (substFormula 0 nil A)] (Formula.impl (PSI A) A)
    refine deduction_aux ?_ (PSI A) _ rfl
    refine PrfH_or_elim (prf_to_prfH (prf_nil_or_consOk (.var 0)) _) ?caso_nil ?caso_cons
    case caso_nil =>
      -- `#0 = nil`: `↑B` es `A[nil]` en el contexto del `∀n`, y Leibniz lo lleva a `A[#0] = A`
      let Γ : List Formula := Formula.eq (.var 0) nil :: PSI A ::
        liftFormula 0 (Formula.forall (Formula.forall (Formula.impl (liftFormula 1 A)
          (substFormula 0 (cons (.var 1) (.var 0)) (liftFormula 2 (liftFormula 1 A)))))) ::
        [liftFormula 0 (substFormula 0 nil A)]
      have hB : PrfH Γ (liftFormula 0 (substFormula 0 nil A)) :=
        PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
      rw [lift0_subst0, ROBINSON_PlusPlus.Minimal.Axioms.liftTerm_nil 0] at hB
      have hn : PrfH Γ ((.var 0) =eq nil) := PrfH.hyp _ _ (List.Mem.head _)
      have hg := PrfH_leibniz_subst (A := liftFormula 1 A) (PrfH_eq_symm hn) hB
      rw [subst0_lift1] at hg
      exact hg
    case caso_cons =>
      -- `#0 = cons h t` con `h = carc #0`, `t = cdrc #0`
      let Γ : List Formula := consOk (.var 0) :: PSI A ::
        liftFormula 0 (Formula.forall (Formula.forall (Formula.impl (liftFormula 1 A)
          (substFormula 0 (cons (.var 1) (.var 0)) (liftFormula 2 (liftFormula 1 A)))))) ::
        [liftFormula 0 (substFormula 0 nil A)]
      have hc : PrfH Γ ((.var 0) =eq cons (carc (.var 0)) (cdrc (.var 0))) :=
        PrfH.hyp _ _ (List.Mem.head _)
      -- la cola es menor
      have hlt : PrfH Γ (lt (cdrc (.var 0)) (.var 0)) :=
        PrfH_lt_subst2 (PrfH_eq_symm hc)
          (prf_to_prfH (prf_cantor_mono_right (carc (.var 0)) (cdrc (.var 0))) _)
      -- `PSI` da `A[cola]`
      have hpsi : PrfH Γ (Formula.forall (Formula.impl (lt (.var 0) (.var 1)) (liftFormula 1 A))) :=
        PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
      have hpi := PrfH_spec hpsi (cdrc (.var 0))
      have epi : substFormula 0 (cdrc (.var 0)) (Formula.impl (lt (.var 0) (.var 1)) (liftFormula 1 A))
          = Formula.impl (lt (cdrc (.var 0)) (.var 0))
              (substFormula 0 (cdrc (.var 0)) (liftFormula 1 A)) := by
        simp only [substFormula, lt, substTerms, substTerm, Nat.reduceEqDiff, Nat.reduceGT,
          Nat.reduceSub, reduceIte, ite_true]
      rw [epi] at hpi
      have hAt := PrfH.mp _ _ _ hpi hlt
      -- `↑S` en `carc #0`, `cdrc #0` da `A[cola] ⇒ A[cons (carc #0) (cdrc #0)]`
      have hS : PrfH Γ (Formula.forall (Formula.forall (liftFormula 2 (Formula.impl (liftFormula 1 A)
          (substFormula 0 (cons (.var 1) (.var 0)) (liftFormula 2 (liftFormula 1 A))))))) :=
        PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
      have hS1 := PrfH_spec hS (carc (.var 0))
      simp only [substFormula] at hS1
      have hS2 := PrfH_spec hS1 (cdrc (.var 0))
      rw [S_inst] at hS2
      have hAc := PrfH.mp _ _ _ hS2 hAt
      -- y Leibniz, de `cons (carc #0) (cdrc #0)` a `#0`
      have hg := PrfH_leibniz_subst (A := liftFormula 1 A) (PrfH_eq_symm hc) hAc
      rw [subst0_lift1] at hg
      exact hg
  exact prf_deduction (deduction_aux hgoal _ _ rfl)

/-- Corolario: la regla DERIVADA de `Meta/ChainPrf.lean` que construye `listInd` (`prf_list_induction`; los demás usos
    del constructor son traducciones, decodificación y `AxiomasT`), con la misma firma y sin `listInd`. -/
theorem prf_list_induction_sin (Φ : Formula)
    (base : Prf (substFormula 0 nil Φ))
    (step : Prf (Formula.forall (Formula.forall (Formula.impl (liftFormula 1 Φ)
              (substFormula 0 (cons (.var 1) (.var 0)) (liftFormula 2 (liftFormula 1 Φ)))))))
    : Prf (Formula.forall Φ) :=
  prf_mp (prf_mp (listInd_admisible Φ) base) step

end ROBINSON_PlusPlus.Meta.ListIndAdmisible

#print axioms ROBINSON_PlusPlus.Meta.ListIndAdmisible.listInd_admisible
#print axioms ROBINSON_PlusPlus.Meta.ListIndAdmisible.prf_strong_ind_formula
#print axioms ROBINSON_PlusPlus.Meta.ListIndAdmisible.prf_nil_or_consOk
#print axioms ROBINSON_PlusPlus.Meta.ListIndAdmisible.prf_list_induction_sin

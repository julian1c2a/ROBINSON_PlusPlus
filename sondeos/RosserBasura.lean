import ROBINSON_PlusPlus

/-!
# Rosser, Etapa 0: la mitad BASURA — refutar en `Prf` la guarda de TÉRMINO sobre un numeral (ADR‑125)

**Fecha**: 2026‑10‑05. Es la segunda pieza de la Etapa 0 del plan de Rosser (ADR‑122 §2; la primera, la reflexión,
en `sondeos/RosserReflexion.lean`): donde la guarda es FALSA, la reflexión no da nada y hay que REFUTARLA en `Prf`.

**Qué dice** (la guarda ENTERA, con su `∃` eliminado, y por primera vez sobre un NUMERAL):

    Prf (¬ hasWit 0̄)                                         -- el 0 (= nil) no es código de término
    Prf (¬ hasWit c)   para c cerrado con Prf (carc c = k̄), k ∉ {0, 1}
    Prf (¬ hasWit ⟨k, r⟩‾)   para todo k ∉ {0, 1} y todo r     -- un numeral, sin hipótesis

**Cómo**: lo que había en `Meta/CodeWitnessPrf.lean` —el refutador de PROFUNDIDAD 1 con testigo abierto
(`prf_crit_In_rejects_open1`) y la forma de pertenencia de `wfAll1` (`prf_isTermCodeE1_of_In`)— más el `∃`‑elim
(`prf_ex_elim_imp`), el puente `∈ → índice` (`prf_boundedIn_of_In`), y, para el numeral, `carc ⟨k, r⟩‾ = k̄` por
`prf_cons_eval`. Lo nuevo: `0 ≠ cons a b` en `Prf` (por los axiomas de lista L1/L2) y la congruencia de `carc`.

⚠️ Lo que NO dice: nada HEREDITARIO —la basura a profundidad 2 (un argumento basura bajo una etiqueta buena) pide
recorrer `argsIn` y evaluar `nthc`/`lenc` sobre el numeral—; nada de `hasWitF`; ni una línea `q1` basura.

## Medido (2026‑10‑05, RPP con ADR‑124)

Compila en 5 s (0,80 GB), 0 errores y 0 avisos; 106 líneas, 7 teoremas. `#print axioms` de los
dos titulares: `[propext, Classical.choice, Quot.sound]`.

## Cómo re‑ejecutarlo

    lake env lean sondeos/RosserBasura.lean      # desde la raíz de RPP
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open FOL
open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.BoundedInPrf
open ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs

namespace RosserBasura

/-! ## §1 · Profundidad 0: el `0` (= `nil`) no es código de término -/

/-- `0 ≠ cons a b` en `Prf`, por los axiomas de lista: `a ∈ cons a b`, y nada está en `nil = 0`. -/
theorem prf_zero_ne_cons (a b : Term) : Prf (Formula.impl (Formula.eq zero (cons a b)) Formula.bottom) := by
  refine prf_deduction ?_
  have hin : PrfH [Formula.eq zero (cons a b)] (In a zero) :=
    PrfH_eq_subst_in (PrfH_eq_symm (prfH_hyp_self _)) (PrfH_in_cons_head a b)
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_not_in_nil a) _) hin

theorem prf_isTermCodeE1_zero_absurd (w : Term) :
    Prf (Formula.impl (isTermCodeE1 w zero) Formula.bottom) :=
  prf_or_elim_imp (prf_zero_ne_cons _ _) (impT (Prf.incl (Prfᵢ.c2 _ _)) (prf_zero_ne_cons _ _))

/-- 🏁 **`¬ hasWit 0̄`**: la guarda ENTERA, con su `∃` eliminado, para CUALQUIER testigo. -/
theorem prf_neg_hasWit_zero : Prf (neg (hasWit (numeralM 0))) := by
  refine prf_ex_elim_imp ?_
  show PrfH [isTC1 (.var 0) zero] Formula.bottom
  have hh := prfH_hyp_self (isTC1 (.var 0) zero)
  have hc := PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (prf_isTermCodeE1_of_In (.var 0) zero) _)
    (PrfH_and_elim_right hh)) (PrfH_and_elim_left hh)
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_isTermCodeE1_zero_absurd (.var 0)) _) hc

/-! ## §2 · Profundidad 1: una etiqueta que no es de término (∉ {0, 1}) -/

/-- La guarda entera, sobre un `c` cerrado de etiqueta `k ∉ {0, 1}`: el `∃`‑elim sobre `prf_crit_In_rejects_open1`. -/
theorem prf_neg_hasWit_tag (c : Term) (k : Nat) (hk0 : k ≠ 0) (hk1 : k ≠ 1)
    (hcl : ∀ n : Nat, liftTerm n c = c) (hck : Prf (carc c =eq numeralM k)) : Prf (neg (hasWit c)) := by
  refine prf_ex_elim_imp ?_
  rw [hcl 0]
  show PrfH [isTC1 (.var 0) c] Formula.bottom
  have hh := prfH_hyp_self (isTC1 (.var 0) c)
  have hb := PrfH.mp _ _ _ (prf_to_prfH (prf_boundedIn_of_In c (.var 0)) _) (PrfH_and_elim_right hh)
  exact PrfH.mp _ _ _ (PrfH.mp _ _ _
    (prf_to_prfH (prf_crit_In_rejects_open1 (.var 0) c k hk0 hk1 hcl hck) _) hb) (PrfH_and_elim_left hh)

/-! ## §3 · Sobre un NUMERAL: `⟨k, r⟩‾`, sin hipótesis -/

theorem prf_congr_carc {x y : Term} (h : Prf (x =eq y)) : Prf (carc x =eq carc y) := by
  let f : Formula := Formula.eq (carc (liftTerm 0 x)) (carc (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (carc x) (carc s) := by
    intro s; simp only [f, substFormula, carc, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS y) ▸ prf_leibniz_subst (A := f) h ((hS x) ▸ prf_refl (carc x))

/-- La etiqueta de un numeral `⟨k, r⟩‾`, en `Prf`: `prf_cons_eval` lo parte en `cons k̄ r̄`. -/
theorem prf_carc_numeral (k r : Nat) : Prf (carc (numeralM (consN k r)) =eq numeralM k) := by
  have h1 := ROBINSON_PlusPlus.Meta.CodeNumeralPrf.prf_cons_eval k r
  rw [← ROBINSON_PlusPlus.Meta.CheckArith.numeralM_eq, ← ROBINSON_PlusPlus.Meta.CheckArith.numeralM_eq,
    ← ROBINSON_PlusPlus.Meta.CheckArith.numeralM_eq] at h1
  exact prf_eq_trans (prf_congr_carc (prf_eq_symm h1)) (prf_carc_cons _ _)

/-- 🏁 **Un numeral basura, refutado**: para TODO `k ∉ {0, 1}` y todo `r`, `Prf (¬ hasWit ⟨k, r⟩‾)`. -/
theorem prf_neg_hasWit_num (k r : Nat) (hk0 : k ≠ 0) (hk1 : k ≠ 1) :
    Prf (neg (hasWit (numeralM (consN k r)))) :=
  prf_neg_hasWit_tag _ k hk0 hk1 (fun n => ROBINSON_PlusPlus.Minimal.Axioms.liftTerm_numeralM n _)
    (prf_carc_numeral k r)

end RosserBasura

#print axioms RosserBasura.prf_neg_hasWit_zero
#print axioms RosserBasura.prf_neg_hasWit_num

/-
SONDA DESECHABLE 3 — NO AÑADIR AL BUILD.

¿Y si se RELATIVIZA el esquema de induccion (para bloquear la sonda 1)?
Tampoco basta: la TRICOTOMIA `ax19` + la definicion del orden `ax13` ya prueban
   forall x. x = 0  or  exists k. x = sigma k
SIN NINGUNA INDUCCION, dentro de Minimal (Robinson Q++) puro.

Luego F2 (cons != nil) + F3 (cons no es sucesor) son inconsistentes con
`ax13 + ax19 + ax2 + ax4 + ax5 + ax6` — todos ellos axiomas de Minimal.
-/
import ROBINSON_PlusPlus.Minimal.Axioms
import FOL.FOL
import FOL.MetaRules
import FOL.Theorems.Eq
import FOL.Theorems.Neg
import FOL.Theorems.Derived
import FOL.Theorems.Quantifiers

set_option linter.unusedSimpArgs false
open FOL ROBINSON_PlusPlus.Minimal.Axioms

namespace OptionBProbe3

/-- **La tricotomia sola ya mata el algebra libre.** Sin induccion, sin ax_L0. -/
theorem free_algebra_kills_in_minimal
    (F2 : ∀ h t : Term, axioms ⊢ neg (cons h t =eq nil))
    (F3 : ∀ h t y : Term, axioms ⊢ neg (cons h t =eq succ y)) :
    axioms ⊢ Formula.bottom := by
  let c : Term := cons zero zero
  -- ax13 instanciado (ida): lt a b  ⇒  ∃k. a + σk = b
  have lt_fwd : ∀ a b : Term, axioms ⊢ lt a b →
      axioms ⊢ Formula.ex (add (liftTerm 0 a) (succ (.var 0)) =eq liftTerm 0 b) := by
    intro a b h
    have hh := spec (spec (ax (by simp [axioms] : ax13_lt_def ∈ axioms)) a) b
    simp [ax13_lt_def, _root_.iff, substFormula, substTerm, substTerms, lt, add, succ,
      FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
    exact iff_mp hh h
  -- tricotomia en (c, 0)
  have htri := spec (spec (ax (by simp [axioms] : ax19_lt_trichotomy ∈ axioms)) c) zero
  simp only [ax19_lt_trichotomy, substFormula, substTerm, substTerms, lt, zero, cons,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift, Nat.reduceEqDiff, Nat.reduceGT,
    reduceIte, if_true] at htri
  refine FOL.MetaRules.or_elim htri ?_ ?_
  · -- c < 0 : imposible (ax13 + ax5 + ax2)
    intro hlt
    have hex := lt_fwd c zero hlt
    simp only [liftTerm, liftTerms, zero, cons] at hex
    apply ex_elim hex; intro k hk
    simp only [substFormula, substTerm, substTerms, add, succ, zero, cons,
      FOL.substTerm_liftTerm, Nat.reduceEqDiff, Nat.reduceGT, reduceIte, if_true] at hk
    -- hk : add c (succ k) =eq zero
    have h5 : axioms ⊢ (add c (succ k) =eq succ (add c k)) := by
      have hh := spec (spec (ax (by simp [axioms] : ax5_add_succ ∈ axioms)) c) k
      simpa [ax5_add_succ, substFormula, substTerm, substTerms, add, succ, cons, zero,
        FOL.substTerm_liftTerm] using hh
    have h2 : axioms ⊢ neg (succ (add c k) =eq zero) := by
      have hh := spec (ax (by simp [axioms] : ax2_peano_succ_neq_zero ∈ axioms)) (add c k)
      simpa [ax2_peano_succ_neq_zero, neg, substFormula, substTerm, substTerms, succ, zero,
        add, cons] using hh
    exact mp h2 (FOL.derive_eq_trans (eq_symm h5) hk)
  · intro hrest
    refine FOL.MetaRules.or_elim hrest ?_ ?_
    · -- c = 0 : F2  (nil := zero, defeq)
      intro h0
      exact mp (F2 zero zero) h0
    · -- 0 < c : entonces c es un sucesor -> F3
      intro hlt
      have hex := lt_fwd zero c hlt
      simp only [liftTerm, liftTerms, zero, cons] at hex
      apply ex_elim hex; intro k hk
      simp only [substFormula, substTerm, substTerms, add, succ, zero, cons,
        FOL.substTerm_liftTerm, Nat.reduceEqDiff, Nat.reduceGT, reduceIte, if_true] at hk
      -- hk : add zero (succ k) =eq c
      have hcomm : axioms ⊢ (add zero (succ k) =eq add (succ k) zero) := by
        have hh := spec (spec (ax (by simp [axioms] : ax6_add_comm ∈ axioms)) zero) (succ k)
        simpa [ax6_add_comm, substFormula, substTerm, substTerms, add, succ, zero,
          FOL.substTerm_liftTerm] using hh
      have h4 : axioms ⊢ (add (succ k) zero =eq succ k) := by
        have hh := spec (ax (by simp [axioms] : ax4_add_zero ∈ axioms)) (succ k)
        simpa [ax4_add_zero, substFormula, substTerm, substTerms, add, succ, zero] using hh
      have hck : axioms ⊢ (c =eq succ k) :=
        FOL.derive_eq_trans (FOL.derive_eq_trans (eq_symm hk) hcomm) h4
      exact mp (F3 zero zero k) hck

end OptionBProbe3

#print axioms OptionBProbe3.free_algebra_kills_in_minimal

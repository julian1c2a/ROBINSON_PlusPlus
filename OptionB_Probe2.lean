/-
SONDA DESECHABLE 2 — NO AÑADIR AL BUILD.

Opcion B en su version DEBIL (algebra libre SIN la disyuncion de formas):
solo F1 (inyectividad de cons) + F2 (cons != nil), SIN ax_L0_cons_def.

Pregunta: ¿basta retirar ax_L0_cons_def para restaurar la consistencia?
Respuesta que aqui se COMPILA: NO. El `boom` se reconstruye sin tocar ax_L0,
usando solo:
  * `zero_or_succ_ax`   (Full/Induction.lean:594, del esquema ax_induction)
  * `cons_neq_nil`      (= F2)
  * `strCode_ne`        (CodeDistinct; su prueba usa SOLO cons_inj = F1, F2, gnum_ne)
  * `ax_tc_succ`, `ax_tc_cons`
-/
import ROBINSON_PlusPlus.Meta.CodeDistinct
import ROBINSON_PlusPlus.Meta.Representability
import ROBINSON_PlusPlus.Full.Induction

set_option linter.unusedSimpArgs false
open FOL ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Minimal.Theorems.Block6
open ROBINSON_PlusPlus.Meta.CodeDistinct
open ROBINSON_PlusPlus.Meta.Representability
open ROBINSON_PlusPlus.Full

namespace OptionBProbe2

/-- El codigo "::"-encabezado de `tcFn (cons 0 0)`. Cerrado. -/
private def Xcons : Term :=
  cons (numeralM 1) (cons (strCodeM cons_sym)
    (cons (cons (tcFn zero) (cons (tcFn zero) nil)) nil))

theorem weak_free_algebra_still_boom : axioms ⊢ Formula.bottom := by
  -- (1) cons 0 0 = 0  ∨  ∃y. cons 0 0 = σy      [zero_or_succ_ax]
  have hzos := spec zero_or_succ_ax (cons zero zero)
  simp only [lor, substFormula] at hzos
  refine FOL.MetaRules.or_elim hzos ?_ ?_
  · -- rama 0: F2
    intro h0
    simp [substFormula, substTerm, substTerms, zero, cons] at h0
    exact mp (cons_neq_nil zero zero) h0
  · -- rama sucesor
    intro hex
    simp only [substFormula, substTerm, substTerms, zero, succ, cons,
      FOL.substTerm_liftTerm, FOL.substTerm_liftLift, Nat.reduceEqDiff, Nat.reduceGT,
      reduceIte, if_true] at hex
    apply ex_elim hex; intro y hy
    simp [substFormula, substTerm, substTerms, zero, succ, cons,
          FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hy
    -- hy : cons 0 0 =eq σ y
    -- (2) ax_tc_cons en (0,0):  tcFn (cons 0 0) = Xcons
    have hc : axioms ⊢ (tcFn (cons zero zero) =eq Xcons) := by
      have hh := spec (spec (ax (by simp [axioms] : ax_tc_cons ∈ axioms)) zero) zero
      simpa [ax_tc_cons, Xcons, substFormula, substTerm, substTerms, tcFn, cons, zero, nil,
             nil, substTerm_numeralM, substTerm_strCodeM, FOL.substTerm_liftTerm] using hh
    -- (3) transporte por hy:  tcFn (σ y) = Xcons
    have hc' : axioms ⊢ (tcFn (succ y) =eq Xcons) := by
      let f : Formula := (tcFn (.var 0) =eq Xcons)
      have hS : ∀ s : Term, substFormula 0 s f = (tcFn s =eq Xcons) := by
        intro s
        simp [f, Xcons, substFormula, substTerm, substTerms, tcFn, cons, zero, nil,
              nil, substTerm_numeralM, substTerm_strCodeM]
      exact (hS (succ y)) ▸ Derives.subst axioms (cons zero zero) (succ y) f hy
        ((hS (cons zero zero)) ▸ hc)
    -- (4) ax_tc_succ en y:  tcFn (σ y) = ⟨1, "σ", [tcFn y]⟩
    have hs : axioms ⊢ (tcFn (succ y) =eq
        cons (numeralM 1) (cons (strCodeM succ_sym) (cons (cons (tcFn y) nil) nil))) := by
      have hh := spec (ax (by simp [axioms] : ax_tc_succ ∈ axioms)) y
      simpa [ax_tc_succ, substFormula, substTerm, substTerms, tcFn, cons, zero, succ,
             nil, substTerm_numeralM, substTerm_strCodeM, FOL.substTerm_liftTerm] using hh
    -- (5) colision de cabezas
    have hcol : axioms ⊢ (cons (numeralM 1) (cons (strCodeM succ_sym)
        (cons (cons (tcFn y) nil) nil)) =eq Xcons) :=
      FOL.derive_eq_trans (eq_symm hs) hc'
    have hne : axioms ⊢ neg (cons (numeralM 1) (cons (strCodeM succ_sym)
        (cons (cons (tcFn y) nil) nil)) =eq Xcons) := by
      simp only [Xcons, strCodeM_eq]
      exact cons_ne_tail (cons_ne_head (strCode_ne (by decide : succ_sym ≠ cons_sym)))
    exact mp hne hcol

end OptionBProbe2

#print axioms OptionBProbe2.weak_free_algebra_still_boom

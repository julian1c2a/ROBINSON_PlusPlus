import ROBINSON_PlusPlus.Meta

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.Sigma1Prf ROBINSON_PlusPlus.Meta.LiftcCodePrf
open ROBINSON_PlusPlus.Meta.DerivCondPrf ROBINSON_PlusPlus.Meta.TrackedCorePrf
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf.ENS (hasWit CRIT_hasWit_real)

set_option maxHeartbeats 1000000

namespace ADV_V2

/-! ### (A) ¿`CRIT_targetLift_real` es un enunciado NUEVO?
     Produccion ya tiene `LiftcCodePrf.refl_termCode : ∀ t, Prf (targetLift (termCode t))`
     y el puente `Representability.termCodeM_eq : termCodeM t = termCode t`. -/

theorem A_CRIT_targetLift_real_YA_ESTA (t : Term) : Prf (targetLift (termCodeM t)) := by
  rw [ROBINSON_PlusPlus.Meta.Representability.termCodeM_eq]
  exact refl_termCode t

theorem A2_CRIT_targetLiftsc_real_YA_ESTA (ts : List Term) :
    Prf (targetLiftsc (termsCodeM ts)) := by
  rw [ROBINSON_PlusPlus.Meta.Representability.termsCodeM_eq]
  exact refl_termsCode ts

/-! ### (B) ¿el `substF_targetLift` del modulo SUBSUME `substF_targetLift_hole`
     (`Meta/LiftcCodePrf.lean:790`, YA en produccion y exportado a raiz)? -/

-- copia literal del §1 del modulo propuesto
theorem substF_targetLift' (v : Nat) (u s : Term) :
    substFormula v u (targetLift s) = targetLift (substTerm v u s) := by
  simp only [targetLift, substFormula_provFromCode_open, eqc, liftcT, funcc, tcFn, liftc,
    cons, nil, zero, succ, substTerm, substTerms, substTerm_termCode, substTerm_strCode]

/-- El de produccion es una INSTANCIA DEFEQ del nuevo (`v := 0`, `s := #0`). -/
theorem B_hole_es_instancia_defeq (t : Term) :
    substF_targetLift_hole t = substF_targetLift' 0 t (.var 0) := rfl

end ADV_V2

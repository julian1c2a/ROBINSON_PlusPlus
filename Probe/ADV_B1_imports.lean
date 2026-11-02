import ROBINSON_PlusPlus.Meta.CodeWitnessPrf

/-! Test: ¿hace falta de verdad el segundo import (`EvalRunFnPrf`)?
    Si `substtc_inv_termCode_numeralM 0` (LineWFSchemaPrf, alcanzable transitivamente por
    CodeWitnessPrf) da lo mismo que `prf_substtc_termCode_nil`, el import sobra. -/

open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.Hilbert

theorem adv_sin_evalrunfn :
    ∀ W, Prf (substtc zero W (termCode zero) =eq termCode zero) :=
  ROBINSON_PlusPlus.Meta.LineWFSchemaPrf.substtc_inv_termCode_numeralM 0

#print axioms adv_sin_evalrunfn

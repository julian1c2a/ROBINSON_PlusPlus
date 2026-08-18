import ROBINSON_PlusPlus.Meta
open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Hilbert ROBINSON_PlusPlus.Meta.Div2ParityPrf
open ROBINSON_PlusPlus.Meta.MpCodePrf

/-- ¿Se puede subir `prf_div2_double` a un ∀ OBJETO? Si sí, `pcc_thm_inst` lo mete
    dentro de `Prov` en cualquier testigo, y el peldaño `div2` NO necesita inducción. -/
theorem prf_div2_double_all :
    Prf (Formula.forall (div2 (mul (.var 0) two) =eq (.var 0))) :=
  Prf.gen _ (prf_div2_double (.var 0))

#print axioms prf_div2_double_all
#check @ROBINSON_PlusPlus.Meta.MpCodePrf.pcc_thm_inst

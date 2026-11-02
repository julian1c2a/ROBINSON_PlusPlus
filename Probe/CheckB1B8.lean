import ROBINSON_PlusPlus.Meta
open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.LiftcCodePrf ROBINSON_PlusPlus.Meta.CodeWitnessPrf

-- B1: el vocabulario de constructores dotados y las clausulas del reflector
#check @liftcT
#check @varcT
#check @targetLift
#check @refl_isTermCodeE1_imp
#check @pcc_liftc_func_code
-- B8: el kit de DISCRIMINACION
#check @ENS.prf_isFormCodeE2_str
#check @ENS.CRIT_isFC1_rejects_varc
-- CONTROL: el decimo duplicado NO entro; se usa el de produccion
-- CONTROL: el decimo duplicado NO entro en produccion (iz_inv no existe)
example : True := by
  fail_if_success (exact ROBINSON_PlusPlus.Meta.LiftcCodePrf.iz_inv)
  trivial

#print axioms ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_isTermCodeE1_imp
#print axioms ROBINSON_PlusPlus.Meta.LiftcCodePrf.pcc_liftc_func_code
#print axioms ROBINSON_PlusPlus.Meta.CodeWitnessPrf.ENS.CRIT_isFC1_rejects_varc

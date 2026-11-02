import ROBINSON_PlusPlus
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs
-- CONTROL POSITIVO: existen, pero SOLO cualificados / bajo `open`
#check @prf_argsIn_head
#check @prf_argsIn_tail
#check @prf_isTermCodeE1_of_boundedIn
#check @prf_isTermCodeE1_of_In

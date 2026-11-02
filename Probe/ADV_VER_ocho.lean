/- ADV_VER_ocho — ¿salen OCHO lemas genericos de §2-§4 de EvalLiftcPrf a la RAIZ?
   Los CUATRO de §2 si. Se espera EXIT 0. -/
import ROBINSON_PlusPlus.Meta

#check @prf_nil_or_cons
#check @prf_nil_or_cons_all
#check @nilOrCons_at
#check @nilOrCons

-- y los que el modulo declara en §3/§4: NINGUNO (bloques de solo docstring).
#check @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.prf_argsIn_head
#check @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.prf_argsIn_tail
#check @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.prf_isTermCodeE1_of_boundedIn
#check @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.prf_isTermCodeE1_of_In

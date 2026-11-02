import ROBINSON_PlusPlus.Meta

open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.CodeWitnessPrf
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.LineWFAssemblePrf
open ROBINSON_PlusPlus.Meta.LineWFSchemaPrf

-- ¿el control POSITIVO descansa en algo sucio?
#print axioms ROBINSON_PlusPlus.Meta.CodeWitnessPrf.HW.prf_hasWitF_real
#print axioms ROBINSON_PlusPlus.Meta.ReprPrf.prf_lineWF_q1
#print axioms ROBINSON_PlusPlus.Meta.LineWFSchemaPrf.pcc_lineWF_tracked_of_schema
#print axioms ROBINSON_PlusPlus.Meta.LineWFAssemblePrf.pcc_lineWF_tracked_of_branches

-- la guarda REAL que arrastra la evaluacion de substfc (produccion)
#check @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.ENS.hasWitF
#check @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.ENS.hasWit

-- ¿`prf_lineWF_q1` acepta A y t ARBITRARIOS? (no hay premisa de buena formacion)
#check @ROBINSON_PlusPlus.Meta.ReprPrf.prf_lineWF_q1

-- el enunciado SIN guarda que hoy consume hC_dot
#check @ROBINSON_PlusPlus.Meta.LineWFAssemblePrf.pcc_lineWF_tracked_of_branches

-- CONTRA-CONTROL: ¿existe ya en PRODUCCION algo que de la guarda desde lineWF?
-- (si existiera, la medicion seria falsa). Se busca por tipo.
example : True := trivial

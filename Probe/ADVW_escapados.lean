/- ADVW · LO QUE SE LE ESCAPO al informe «substtc:conexion».
   Dos de los 73 nombres que declara «faltan por nombre, hay que promoverlos» son
   DUPLICADOS SEMANTICOS de produccion, con nombre distinto. Aqui, compilados.
   Mismos `open` que el sondeo (ninguno de los cuatro que el informe propone anadir). -/
import ROBINSON_PlusPlus.Meta

open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.TcArithPrf ROBINSON_PlusPlus.Meta.CheckArith
open ROBINSON_PlusPlus.Meta.Sigma1Prf ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
open ROBINSON_PlusPlus.Meta.MpCodePrf ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf
open ROBINSON_PlusPlus.Meta.NumCodeClosedPrf ROBINSON_PlusPlus.Meta.EvalArithPrf

namespace ADVWesc

/-- Copia LITERAL del sondeo, `sondeos/EvalSubsttc.lean:64`. -/
theorem eqc_eq_eqCodeFn (a b : Term) : eqc a b = eqCodeFn a b :=
  (ROBINSON_PlusPlus.Meta.Sigma1AtomPrf.eqCodeFn_eq_eqc a b).symm

/-- Copia LITERAL del sondeo, `sondeos/EvalSubsttc.lean:1788-1794`, cerrada con la
    constante de PRODUCCION `EvalPredPrf.pcc_ax26_computed` instanciada en `w := tcFn m`. -/
theorem pcc_pred_succ_code (m : Term) :
    Prf (provFromCode (eqCodeFn
      (ROBINSON_PlusPlus.Meta.EvalPredPrf.predcT (succcT (tcFn m))) (tcFn m))) :=
  ROBINSON_PlusPlus.Meta.EvalPredPrf.pcc_ax26_computed (tcFn m)

/-- Y produccion ya tiene ADEMAS el puente de orientacion escrito, exportado o no. -/
theorem chk_bridge_ya_escrito (a b : Term) : eqc a b = eqCodeFn a b :=
  ROBINSON_PlusPlus.Meta.EvalLiftcPrf.eqc_eq_eqCodeFn_es_symm a b

end ADVWesc

#print axioms ADVWesc.eqc_eq_eqCodeFn
#print axioms ADVWesc.pcc_pred_succ_code

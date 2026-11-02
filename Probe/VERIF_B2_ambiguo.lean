import ROBINSON_PlusPlus.Meta.CodeWitnessPrf

/-! CONTROL NEGATIVO del verificador: si `ENS` NO re-declarase los cinco lemas que ya
    estan en `SinWTs`, este fichero compilaria. Se espera FALLO por ambiguedad. -/

open ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf.ENS

open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel

example (k : Nat) (wT Y : Term) :
    liftFormula k (argsIn wT Y) = argsIn (liftTerm k wT) (liftTerm k Y) :=
  liftF_argsIn k wT Y

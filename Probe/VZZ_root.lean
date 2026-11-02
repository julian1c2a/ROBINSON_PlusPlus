import ROBINSON_PlusPlus
import Lean
open Lean Elab Command

/-! ¿Qué sale realmente A LA RAIZ? -/

run_cmd do
  let env ← getEnv
  let cands : List Name :=
    [ `ROBINSON_PlusPlus.Meta.nilOrCons
    , `ROBINSON_PlusPlus.Meta.nilOrCons_at
    , `ROBINSON_PlusPlus.Meta.prf_nil_or_cons_all
    , `ROBINSON_PlusPlus.Meta.prf_nil_or_cons
    , `ROBINSON_PlusPlus.Meta.prf_argsIn_head
    , `ROBINSON_PlusPlus.Meta.prf_argsIn_tail
    , `ROBINSON_PlusPlus.Meta.prf_isTermCodeE1_of_boundedIn
    , `ROBINSON_PlusPlus.Meta.prf_isTermCodeE1_of_In
    , `ROBINSON_PlusPlus.Meta.liftF_targetLift
    , `ROBINSON_PlusPlus.Meta.liftF_targetLiftsc
    , `ROBINSON_PlusPlus.Meta.substF_targetLift
    , `ROBINSON_PlusPlus.Meta.substF_targetLiftsc
    , `ROBINSON_PlusPlus.Meta.pcc_eval_liftc
    , `ROBINSON_PlusPlus.Meta.PrfH_eq_trans_code
    ]
  for c in cands do
    logInfo s!"ALIAS-o-CONST {c} : {(env.find? c).isSome} / alias={(getAliasState env).find? c |>.length}"

-- control positivo: los cuatro de §2 SI resuelven sin cualificar
#check @nilOrCons
#check @nilOrCons_at
#check @prf_nil_or_cons_all
#check @prf_nil_or_cons
#check @pcc_eval_liftc
#check @substF_targetLift
#check @PrfH_eq_trans_code

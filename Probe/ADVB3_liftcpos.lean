/- Posicion de `Meta/LiftcCodePrf.lean` para `prf_substtc_binK_at`: importo SUS imports
   (lineas 1-25) y NADA mas. NO importo LiftcCodePrf ni el barrel.
   Cada identificador de la prueba de `prf_substtc_binK_at` que NO sea `binK`,
   `prf_substtc_termCode_closed` ni `prf_substtc_termCode_zero` DEBE resolver aqui:
   eso prueba que todo lo demas es AGUAS ARRIBA de LiftcCodePrf. -/
import ROBINSON_PlusPlus.Meta.ArithPrf
import ROBINSON_PlusPlus.Meta.ChainPrf
import ROBINSON_PlusPlus.Meta.CodeCtorKit
import ROBINSON_PlusPlus.Meta.CodeWitnessPrf
import ROBINSON_PlusPlus.Meta.Delta0ReflectPrf
import ROBINSON_PlusPlus.Meta.DerivCondPrf
import ROBINSON_PlusPlus.Meta.DotConsPrf
import ROBINSON_PlusPlus.Meta.EvalArithPrf
import ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf
import ROBINSON_PlusPlus.Meta.EvalLtPrf
import ROBINSON_PlusPlus.Meta.Godel
import ROBINSON_PlusPlus.Meta.Hilbert
import ROBINSON_PlusPlus.Meta.HilbertDeduction
import ROBINSON_PlusPlus.Meta.LineWFTrackedPrf
import ROBINSON_PlusPlus.Meta.MpCodePrf
import ROBINSON_PlusPlus.Meta.NatArithPrf
import ROBINSON_PlusPlus.Meta.NumCodeClosedPrf
import ROBINSON_PlusPlus.Meta.Provability
import ROBINSON_PlusPlus.Meta.ReprPrf
import ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
import ROBINSON_PlusPlus.Meta.Sigma1Prf
import ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf
import ROBINSON_PlusPlus.Meta.TcArithPrf
import ROBINSON_PlusPlus.Meta.TrackedCorePrf
import ROBINSON_PlusPlus.Meta.EvalRunFnPrf

open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.DotConsPrf
open ROBINSON_PlusPlus.Meta.CodeCtorKit ROBINSON_PlusPlus.Meta.NumCodeClosedPrf
open ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf ROBINSON_PlusPlus.Meta.ArithPrf

-- CONTROL: LiftcCodePrf NO esta importado.
-- (si lo estuviera, `prf_substtc_termCode_closed` resolveria)
#check @prf_substtc_funcc2
#check @prf_congr_funcc2
#check @prf_congr_cons_head
#check @prf_congr_cons_tail
#check @prf_eq_trans
#check @consT
#check @termCode
#check @binT

import ROBINSON_PlusPlus.Meta

/-! AUDITORIA ADVERSARIAL — direccion CONTRARIA: ¿hay duplicados que el agente NO declaro?
    Cada `theorem ... := rfl` obliga a que los DOS TIPOS sean defeq. Si no lo son, no compila. -/

open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.TcArithPrf ROBINSON_PlusPlus.Meta.Sigma1Prf
open ROBINSON_PlusPlus.Meta.Sigma1AtomPrf ROBINSON_PlusPlus.Meta.MpCodePrf
open ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf ROBINSON_PlusPlus.Meta.NumCodeClosedPrf
open ROBINSON_PlusPlus.Meta.EvalArithPrf ROBINSON_PlusPlus.Meta.EvalLtPrf
open ROBINSON_PlusPlus.Meta.NatArithPrf ROBINSON_PlusPlus.Meta.DotConsPrf
open ROBINSON_PlusPlus.Meta.DerivCondPrf ROBINSON_PlusPlus.Meta.CodeCtorKit
open ROBINSON_PlusPlus.Meta.HilbertDeduction ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf ROBINSON_PlusPlus.Meta.TrackedCorePrf
open ROBINSON_PlusPlus.Meta.LineWFTrackedPrf

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace ADVDUP

-- ── copias literales de B1_mecanica.lean de los candidatos sospechosos ──

def varcT (X : Term) : Term := unT 0 X
def funccT (X Y : Term) : Term := binT 1 X Y

theorem varcT_termCode (x : Term) : varcT (termCode x) = termCode (varc x) := rfl
theorem funccT_termCode (x y : Term) : funccT (termCode x) (termCode y) = termCode (funcc x y) :=
  rfl

theorem prf_congr_varcT {X X' : Term} (h : Prf (X =eq X')) : Prf (varcT X =eq varcT X') :=
  prf_congr_unT h
theorem prf_congr_funccT {X X' Y Y' : Term} (hx : Prf (X =eq X')) (hy : Prf (Y =eq Y')) :
    Prf (funccT X Y =eq funccT X' Y') := prf_congr_binT hx hy

theorem prf_substtc_termCode_closed (v : Nat) (W t : Term) (ht : ∀ c : Nat, liftTerm c t = t) :
    Prf (substtc (numeral v) W (termCode t) =eq termCode t) := by
  have h := prf_substtc_arith_open v W t
  rwa [substCodeT_closed v W t ht] at h

theorem prf_substtc_termCode_zero (v : Nat) (W : Term) :
    Prf (substtc (numeral v) W (termCode zero) =eq termCode zero) :=
  prf_substtc_termCode_closed v W zero (fun _ => rfl)

theorem iz_inv : ∀ W, Prf (substtc zero W (termCode zero) =eq termCode zero) :=
  fun W => prf_substtc_termCode_zero 0 W

end ADVDUP

-- ══════ ¿DUPLICADOS NO DECLARADOS? cada `rfl` que compile = duplicado real ══════

/-! ### 1 · `iz_inv` -/
theorem adv_iz_inv_vs_nil :
    @ADVDUP.iz_inv = @ROBINSON_PlusPlus.Meta.EvalRunFnPrf.prf_substtc_termCode_nil := rfl

theorem adv_iz_inv_vs_numeralM :
    @ADVDUP.iz_inv
      = ROBINSON_PlusPlus.Meta.LineWFSchemaPrf.substtc_inv_termCode_numeralM 0 := rfl

/-! ### 2 · los alias `varcT`/`funccT` sobre el KIT -/
theorem adv_varcT_termCode :
    @ADVDUP.varcT_termCode = fun x => ROBINSON_PlusPlus.Meta.CodeCtorKit.unT_termCode 0 x := rfl
theorem adv_funccT_termCode :
    @ADVDUP.funccT_termCode
      = fun x y => ROBINSON_PlusPlus.Meta.CodeCtorKit.binT_termCode 1 x y := rfl
theorem adv_congr_varcT :
    @ADVDUP.prf_congr_varcT = @ROBINSON_PlusPlus.Meta.CodeCtorKit.prf_congr_unT 0 := rfl
theorem adv_congr_funccT :
    @ADVDUP.prf_congr_funccT = @ROBINSON_PlusPlus.Meta.CodeCtorKit.prf_congr_binT 1 := rfl

/-! ### 3 · CONTROL POSITIVO DEL METODO: cosas que NO son duplicados deben FALLAR. -/
example : True := by
  fail_if_success
    exact (rfl : @ADVDUP.prf_congr_varcT = @ROBINSON_PlusPlus.Meta.CodeCtorKit.prf_congr_unT 1)
  trivial

example : True := by
  fail_if_success
    exact (rfl : @ADVDUP.iz_inv
      = ROBINSON_PlusPlus.Meta.LineWFSchemaPrf.substtc_inv_termCode_numeralM 1)
  trivial

#print axioms adv_iz_inv_vs_nil

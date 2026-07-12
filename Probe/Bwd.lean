import ROBINSON_PlusPlus.Meta
open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.RunFnBoundedPrf
open ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf ROBINSON_PlusPlus.Meta.EvalListPrf
open ROBINSON_PlusPlus.Meta.EvalNthcPrf ROBINSON_PlusPlus.Meta.EvalRunFnPrf
open ROBINSON_PlusPlus.Meta.TrackedCorePrf ROBINSON_PlusPlus.Meta.EvalBoundedPrf
open ROBINSON_PlusPlus.Meta.Delta0ReflectPrf ROBINSON_PlusPlus.Meta.D3DottedPrf

def phiBwdP (φ : Formula) : Formula :=
  Formula.impl (boundedCarcIn (formCode φ) (.var 0)) (In (formCode φ) (runFn nil (.var 0)))

-- (1) substCodeF forma explicita
example (φ : Formula) : substCodeF 0 (tcFn (.var 0)) (phiBwdP φ) =
    implc
      (exc (andc
        (ltCodeFn (varc (numeral 0)) (lencT (liftc zero (tcFn (.var 0)))))
        (eqCodeFn (carcT (nthcT (liftc zero (tcFn (.var 0))) (varc (numeral 0))))
          (termCode (formCode φ)))))
      (atom2CodeFn in_sym (termCode (formCode φ)) (runFnT (termCode nil) (tcFn (.var 0)))) := rfl

-- (2) el consecuente computado ES inDot (via prf_substfc_arith_open, no rfl):
example (φ : Formula) : Prf (inDot φ =eq
    atom2CodeFn in_sym (termCode (formCode φ)) (runFnT (termCode nil) (tcFn (.var 0)))) :=
  prf_substfc_arith_open 0 (tcFn (.var 0)) (In (formCode φ) (runFn nil (.var 0)))

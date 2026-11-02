/- ADVERSARIAL: ¿es MedBin (8 decls) REALMENTE supersedido por SubstfcCodePrf? -/
import ROBINSON_PlusPlus.Meta.SubstfcCodePrf

open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.SubstfcCodePrf

namespace ADVMED

/-- Copia LITERAL de sondeos/SubstfcEx.lean:4544 -/
def bnc (m : Nat) (a b : Term) : Term := cons (numeralM m) (cons a (cons b nil))
/-- Copia LITERAL de sondeos/SubstfcEx.lean:4551 -/
def AXBODY2 (m : Nat) : Formula :=
  substfc (.var 3) (.var 2) (bnc m (.var 1) (.var 0))
    =eq bnc m (substfc (.var 3) (.var 2) (.var 1)) (substfc (.var 3) (.var 2) (.var 0))

-- PUENTES por rfl con produccion
example (m : Nat) (a b : Term) : bnc m a b = binct (numeralM m) a b := rfl
example (m : Nat) : AXBODY2 m = AXBIN_BODY (numeralM m) := rfl

-- Las 6 casillas restantes de MedBin, probadas SOLO con las de produccion
theorem X_bnc5 (a b : Term) : bnc 5 a b = implc a b := binct_implc a b
theorem X_bnc7 (a b : Term) : bnc 7 a b = andc a b := binct_andc a b
theorem X_bnc8 (a b : Term) : bnc 8 a b = orc a b := binct_orc a b
theorem X_AXBODY2_impl : ax_substfc_impl = forall_4 (AXBODY2 5) := AXBIN_impl
theorem X_AXBODY2_and  : ax_substfc_and  = forall_4 (AXBODY2 7) := AXBIN_and
theorem X_AXBODY2_or   : ax_substfc_or   = forall_4 (AXBODY2 8) := AXBIN_or

-- CONTROL: produccion es ESTRICTAMENTE mas general (tag Term abstracto).
-- Si `binct` solo aceptase Nat, esto NO elaboraria.
example (T a b : Term) : Term := binct T a b
-- CONTROL NEGATIVO: el puente no es vacuo.
example : True := by
  fail_if_success (exact (rfl : ax_substfc_eq = forall_4 (AXBODY2 4)))
  trivial

end ADVMED

#print axioms ADVMED.X_AXBODY2_impl
#print axioms ADVMED.X_bnc5

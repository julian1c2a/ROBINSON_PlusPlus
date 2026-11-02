/-
  CONTROL NEGATIVO del audit de `Probe/Ctor_generico.lean`.

  Objetivo: comprobar que el puente `_termCode` por `rfl` es DISCRIMINANTE, es decir,
  que un `strCode` con el NOMBRE EQUIVOCADO **no** compilaría. Este fichero DEBE FALLAR.
-/
import ROBINSON_PlusPlus.Meta

open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability

namespace VerifNeg

/-- Constructor de código con el nombre EQUIVOCADO (`liftc` en vez de `substfc`). -/
def substfcT_MAL (v s f : Term) : Term :=
  funcc (strCode "liftc") (cons v (cons s (cons f nil)))

/-- Este puente DEBE fallar: el símbolo no coincide con el de `substfc`. -/
theorem substfcT_MAL_termCode (a b c : Term) :
    substfcT_MAL (termCode a) (termCode b) (termCode c) = termCode (substfc a b c) := rfl

/-- Y este también: aridad correcta, símbolo cambiado (`substtc` vs `substtsc`). -/
def substtcT_MAL (v s t : Term) : Term :=
  funcc (strCode "substtsc") (cons v (cons s (cons t nil)))

theorem substtcT_MAL_termCode (a b c : Term) :
    substtcT_MAL (termCode a) (termCode b) (termCode c) = termCode (substtc a b c) := rfl

end VerifNeg

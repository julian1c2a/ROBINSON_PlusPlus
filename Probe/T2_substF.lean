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

/-!
# `Probe/T2_substF.lean` — ¿puede BAJAR `substF_targetLift` a `LiftcCodePrf`?

MEDICION, no opinion. La pregunta es si el lema GENERAL
`EvalLiftcPrf.substF_targetLift` (`Meta/EvalLiftcPrf.lean:228`) puede declararse en
`Meta/LiftcCodePrf.lean` **en el punto de la linea 790**, dejando alli el particular
`substF_targetLift_hole` como corolario.

## Metodo

Los `import` de arriba son **BYTE A BYTE los 25 de `Meta/LiftcCodePrf.lean:1-25`**.
NO se importa `EvalLiftcPrf`, NO se importa el barrel `ROBINSON_PlusPlus.Meta`, y
**NO se importa `LiftcCodePrf`**: si se importara, todo lo que `LiftcCodePrf` declara
DESPUES de la linea 790 estaria en scope y la medida no valdria.

Por eso §0 recrea, **copiadas byte a byte de su sitio**, las UNICAS tres declaraciones
de `LiftcCodePrf` anteriores a `:790` que el lema general necesita:

  * `liftcT`                                   (`LiftcCodePrf.lean:105`)
  * `targetLift`                               (`LiftcCodePrf.lean:225`)
  * `substTerm_termCode` / `substTerm_termsCode` (`LiftcCodePrf.lean:775-787`, el bloque
    `mutual` INMEDIATAMENTE anterior a `:790`)

Todo lo demas que usan enunciado y prueba viene de modulos que `LiftcCodePrf` YA importa.
-/

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
open ROBINSON_PlusPlus.Meta.LineWFTrackedPrf ROBINSON_PlusPlus.Meta.EvalRunFnPrf

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

namespace Probe.T2

/-! ############################################################################
    ## §0 · EL PREFIJO DE `LiftcCodePrf` ANTERIOR A `:790`, copiado byte a byte
    ############################################################################ -/

/-- Copia de `Meta/LiftcCodePrf.lean:105`. -/
def liftcT (c t : Term) : Term := funcc (strCode "liftc") (cons c (cons t nil))

/-- Copia de `Meta/LiftcCodePrf.lean:225`. -/
def targetLift (s : Term) : Formula :=
  provFromCode (eqc (liftcT (termCode zero) (tcFn s)) (tcFn (liftc zero s)))

/-! Copia de `Meta/LiftcCodePrf.lean:775-787` (el `mutual` inmediatamente anterior a `:790`). -/
mutual
theorem substTerm_termCode (v : Nat) (u : Term) :
    ∀ t : Term, substTerm v u (termCode t) = termCode t
  | .var _ => by simp only [termCode, cons, nil, zero, substTerm, substTerms, substTerm_numeral]
  | .func s ts => by
      simp only [termCode, cons, nil, zero, substTerm, substTerms, substTerm_numeral,
        substTerm_strCode, substTerm_termsCode v u ts]
theorem substTerm_termsCode (v : Nat) (u : Term) :
    ∀ ts : List Term, substTerm v u (termsCode ts) = termsCode ts
  | []      => rfl
  | t :: ts => by
      simp only [termsCode, cons, substTerm, substTerms, substTerm_termCode v u t,
        substTerm_termsCode v u ts]
end

/-! ############################################################################
    ## §1 · EL LEMA GENERAL, RE-DEMOSTRADO EN EL PUNTO DE `LiftcCodePrf:790`
    ############################################################################

    Enunciado y prueba son la COPIA LITERAL de `Meta/EvalLiftcPrf.lean:228-231`.
    Si esto compila con SOLO los imports de `LiftcCodePrf` + el prefijo §0, el lema
    general PUEDE BAJAR. -/

theorem substF_targetLift (v : Nat) (u s : Term) :
    substFormula v u (targetLift s) = targetLift (substTerm v u s) := by
  simp only [targetLift, substFormula_provFromCode_open, eqc, liftcT, funcc, tcFn, liftc,
    cons, nil, zero, succ, substTerm, substTerms, substTerm_termCode, substTerm_strCode]

/-! ############################################################################
    ## §2 · EL COROLARIO: el enunciado de `LiftcCodePrf:790`, VERBATIM
    ############################################################################

    El bloque de abajo es el enunciado de `Meta/LiftcCodePrf.lean:790-794` copiado sin
    tocar una coma. Solo cambia la PRUEBA: en vez del `simp only` propio, es la instancia
    `v := 0`, `u := t`, `s := #0` del general — y sale por aplicacion directa, sin
    conversion explicita, o sea que los dos tipos son DEFEQ. -/

theorem substF_targetLift_hole (t : Term) :
    substFormula 0 t (provFromCode (eqc (liftcT (termCode zero) (tcFn (.var 0)))
        (tcFn (liftc zero (.var 0)))))
      = targetLift t :=
  substF_targetLift 0 t (.var 0)

/-- CONTROL EXPLICITO de la defeq de los DOS TIPOS (no solo de los habitantes):
    el tipo del corolario y el tipo de la instancia del general son el MISMO. -/
example (t : Term) :
    (substFormula 0 t (provFromCode (eqc (liftcT (termCode zero) (tcFn (.var 0)))
        (tcFn (liftc zero (.var 0)))))
      = targetLift t)
    = (substFormula 0 t (targetLift (.var 0)) = targetLift (substTerm 0 t (.var 0))) := rfl

/-! ############################################################################
    ## §3 · LOS CONSUMIDORES INTERNOS DE `:799` y `:802` SIGUEN FUNCIONANDO
    ############################################################################

    `PrfH_congr_targetLift` (`LiftcCodePrf.lean:797-802`) es el UNICO consumidor de
    `substF_targetLift_hole` en produccion (fuera de la lista `export` de `:1010` y del
    `#print axioms` de `:1038`). Se copia byte a byte y se comprueba que compila contra
    el corolario de §2. -/

theorem PrfH_congr_targetLift {Γ : List Formula} {s s' : Term} (h : PrfH Γ (s =eq s'))
    (ha : PrfH Γ (targetLift s)) : PrfH Γ (targetLift s') :=
  (substF_targetLift_hole s') ▸
    PrfH_leibniz_subst
      (A := provFromCode (eqc (liftcT (termCode zero) (tcFn (.var 0)))
        (tcFn (liftc zero (.var 0))))) h ((substF_targetLift_hole s) ▸ ha)

/-! ### §3b · La misma prueba, pero pasando por el GENERAL sin corolario intermedio.
     Sirve para medir que el corolario no es imprescindible: el `▸` acepta igual el
     lema de tres parametros. (No se propone hacerlo asi; es solo la medida.) -/

theorem PrfH_congr_targetLift_directo {Γ : List Formula} {s s' : Term}
    (h : PrfH Γ (s =eq s')) (ha : PrfH Γ (targetLift s)) : PrfH Γ (targetLift s') :=
  (substF_targetLift 0 s' (.var 0)) ▸
    PrfH_leibniz_subst
      (A := provFromCode (eqc (liftcT (termCode zero) (tcFn (.var 0)))
        (tcFn (liftc zero (.var 0))))) h ((substF_targetLift 0 s (.var 0)) ▸ ha)

/-! ############################################################################
    ## §4 · EL «SIMP-SET DE `:1010`» NO EXISTE — ES LA LISTA `export`
    ############################################################################

    La tarea avisaba de un riesgo: «un lema con MAS parametros no dispara igual en
    `simp only`». MEDIDO: `Meta/LiftcCodePrf.lean:1010` **no es un `simp only`**. Es una
    linea de la clausula `export ROBINSON_PlusPlus.Meta.LiftcCodePrf (…)` que abre en
    `:989` y cierra en `:1014`. `substF_targetLift_hole` aparece alli como NOMBRE
    exportado a la raiz, no como lema de reescritura. El riesgo no aplica.

    Y `substF_targetLift_hole` **NO se usa en ningun `simp only`/`rw` de produccion**:
    sus unicas tres ocurrencias fuera de su propia declaracion son `:799`, `:802`
    (ambas por `▸`, §3) y las dos lineas administrativas `:1010` (export) y `:1038`
    (`#print axioms`). -/

/-! ############################################################################
    ## §5 · CONTROL NEGATIVO — el general NO es trivial
    ############################################################################ -/

example (u s : Term) : True := by
  fail_if_success
    exact (rfl : substFormula 0 u (targetLift s) = targetLift (substTerm 0 u s))
  trivial

/-! ############################################################################
    ## §6 · BONUS MEDIDO — el GEMELO `substF_targetLiftsc` baja tambien
    ############################################################################

    No lo pedia la tarea, pero comparte footprint exacto: `liftscT` esta en
    `LiftcCodePrf.lean:107` y `targetLiftsc` en `:229`, los dos antes de `:790`. Se mide
    para que la bajada pueda hacerse de una sola vez y no quede el par partido en dos
    modulos. -/

/-- Copia de `Meta/LiftcCodePrf.lean:107`. -/
def liftscT (c ts : Term) : Term := funcc (strCode "liftsc") (cons c (cons ts nil))

/-- Copia de `Meta/LiftcCodePrf.lean:229`. -/
def targetLiftsc (b : Term) : Formula :=
  provFromCode (eqc (liftscT (termCode zero) (tcFn b)) (tcFn (liftsc zero b)))

/-- Copia literal de `Meta/EvalLiftcPrf.lean:233-236`. -/
theorem substF_targetLiftsc (v : Nat) (u s : Term) :
    substFormula v u (targetLiftsc s) = targetLiftsc (substTerm v u s) := by
  simp only [targetLiftsc, substFormula_provFromCode_open, eqc, liftscT, funcc, tcFn, liftsc,
    cons, nil, zero, succ, substTerm, substTerms, substTerm_termCode, substTerm_strCode]

end Probe.T2

/-! ## CONTROL DE FOOTPRINT — debe salir NET-0 sobre la base sancionada. -/

#print axioms Probe.T2.substF_targetLift
#print axioms Probe.T2.substF_targetLift_hole
#print axioms Probe.T2.PrfH_congr_targetLift
#print axioms Probe.T2.PrfH_congr_targetLift_directo
#print axioms Probe.T2.substF_targetLiftsc

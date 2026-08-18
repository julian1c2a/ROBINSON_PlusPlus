/-
PILOTO DE LA CAPA RASTREADA — ¿sobrevive a la vía numeral?

EL NUDO. `pcc_eval_carc (h t)` (EvalListPrf.lean:141‑157) toma `h`,`t` **ABSTRACTOS** y usa
`prf_tc_cons' h t : tcFn (cons h t) =eq consT (tcFn h) (tcFn t)`. Toda la capa rastreada (los 14
tags, `hI_dot`, el KIT de `CodeCtorKit`) cuelga de ahí.

LA PREGUNTA: ¿es esa ecuación compatible con la lectura NUMERAL de `tcFn`?

EL TEST. Con `prf_cons_eval` (ya demostrado) se puede AHORA enfrentar las dos lecturas sin rodeos:
`cons 0 nil =eq numeral 2` es demostrable, luego por congruencia de `tcFn` los dos lados tienen que
dar el mismo código. Si `prf_tc_cons` y `prf_tc_numeral` discrepan ahí, son incompatibles.
-/
import ROBINSON_PlusPlus.Meta.CodeNumeralPrf
import ROBINSON_PlusPlus.Meta.TcArithPrf

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.TcArithPrf
open ROBINSON_PlusPlus.Meta.CodeNumeralPrf

namespace PilotoRastreada

/-! ### 1 · El valor: `cons 0 nil = 2`, ahora DEMOSTRABLE (antes se argumentaba) -/

example : consN 0 0 = 2 := rfl

/-- `cons 0 nil =eq numeral 2` — instancia de `prf_cons_eval`. -/
theorem prf_cons_zero_nil : Prf (cons zero nil =eq numeral 2) := prf_cons_eval 0 0

/-! ### 2 · Las dos lecturas, enfrentadas sobre ESE valor

* lectura **NUMERAL** (`prf_tc_numeral`, la consistente, la que usa el diagonal reparado):
  `tcFn (cons 0 nil) = tcFn (numeral 2) = termCode (numeral 2)`, cabeza `⌜σ⌝`.
* lectura **SINTÁCTICA** (`prf_tc_cons`, la que la capa rastreada necesita **sobre argumentos
  abstractos**): `tcFn (cons 0 nil) = ⟨1,⌜::⌝,[tcFn 0, tcFn 0]⟩`, cabeza `⌜::⌝`. -/

/-- Vía NUMERAL. Usa sólo `ax_tc_zero`/`ax_tc_succ` + `prf_cons_eval`. -/
theorem via_numeral : Prf (tcFn (cons zero nil) =eq termCode (numeral 2)) :=
  prf_eq_trans (prf_congr_tcFn prf_cons_zero_nil) (prf_tc_numeral 2)

/-- Vía SINTÁCTICA. Es `prf_tc_cons`, o sea `ax_tc_cons`. -/
theorem via_sintactica :
    Prf (tcFn (cons zero nil) =eq
      cons (numeral 1) (cons (strCode cons_sym)
        (cons (cons (tcFn zero) (cons (tcFn nil) nil)) nil))) :=
  prf_tc_cons zero nil

/-- **LAS DOS JUNTAS**: la teoría prueba que un código de cabeza `⌜::⌝` es uno de cabeza `⌜σ⌝`. -/
theorem choque :
    Prf (cons (numeral 1) (cons (strCode cons_sym)
          (cons (cons (tcFn zero) (cons (tcFn nil) nil)) nil))
      =eq termCode (numeral 2)) :=
  prf_eq_trans (prf_eq_symm via_sintactica) via_numeral

/-- Y los dos lados son, META, códigos con cabeza distinta: `⌜::⌝` vs `⌜σ⌝`. -/
example : termCode (numeral 2) =
    cons (numeral 1) (cons (strCode succ_sym)
      (cons (cons (termCode (numeral 1)) nil) nil)) := rfl

example : cons_sym ≠ succ_sym := by decide

end PilotoRastreada

#print axioms PilotoRastreada.prf_cons_zero_nil
#print axioms PilotoRastreada.via_numeral
#print axioms PilotoRastreada.choque

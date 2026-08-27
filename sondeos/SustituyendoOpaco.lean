/- ③ · RECONOCIMIENTO — ¿hace falta `pcc_eval_liftc` (clausura de `isTermCode` bajo `liftc`)?

   El gate (`sondeos/ClausuraNoHaceFalta.lean` y su síntesis) afirmó:

     «(B) Dentro de `pcc_eval_substfc`, casos ∀/∃ — `ax_substfc_forall/ex` es la ÚNICA familia
      cuyo paso recursivo cambia un parámetro por una APLICACIÓN DE FUNCIÓN: el sustituyendo pasa
      de `s` a `liftc zero s`. Eso obliga a `pcc_eval_liftc` ⇒ clausura de `isTermCode` bajo
      `liftc`, a profundidad de binder arbitraria dentro de un código abstracto.»

   ⚠️ Ese mismo informe ya se equivocó una vez de la misma manera: dijo que faltaba el puente
   `In x w → ∃i<lenc w. nthc w i = x` cuando **estaba en producción**. Infirió una obligación de
   la PRESENCIA SINTÁCTICA de un símbolo sin comprobar si algo lo inspecciona.

   ## RESULTADO: la afirmación es FALSA. El sustituyendo es CARGA OPACA.

   Las tres comprobaciones de abajo, todas compiladas. -/
import ROBINSON_PlusPlus.Meta

open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Hilbert ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf

namespace SustituyendoOpaco

/-! ## 1 · La recursión del `∀` mete `liftc zero w` y NO pide NADA de él — por `rfl` -/

theorem forall_recurre_en_liftc (v : Nat) (w : Term) (a : Formula) :
    substCodeF v w (Formula.forall a)
      = cons (numeral 6) (cons (substCodeF (v + 1) (liftc zero w) a) nil) := rfl

theorem ex_recurre_en_liftc (v : Nat) (w : Term) (a : Formula) :
    substCodeF v w (Formula.ex a)
      = cons (numeral 9) (cons (substCodeF (v + 1) (liftc zero w) a) nil) := rfl

/-! ## 2 · Y la ECUACIÓN se prueba con el sustituyendo ABSTRACTO, cero hipótesis

    `prf_substfc_arith_open` está **en producción** (`SubstCodeOpenPrf.lean:138`) y su `w` es un
    `Term` pelado. Cubre los 8 constructores, `∀`/`∃` incluidos. -/

theorem eq_forall_w_abstracto (v : Nat) (w : Term) (a : Formula) :
    Prf (substfc (numeral v) w (formCode (Formula.forall a))
      =eq substCodeF v w (Formula.forall a)) :=
  prf_substfc_arith_open v w (Formula.forall a)

theorem eq_ex_w_abstracto (v : Nat) (w : Term) (a : Formula) :
    Prf (substfc (numeral v) w (formCode (Formula.ex a))
      =eq substCodeF v w (Formula.ex a)) :=
  prf_substfc_arith_open v w (Formula.ex a)

/-! ## 3 · El caso que la clausura pretendía excluir: sustituyendo LITERALMENTE una variable -/

theorem eq_forall_w_es_var0 (v : Nat) (a : Formula) :
    Prf (substfc (numeral v) (Term.var 0) (formCode (Formula.forall a))
      =eq substCodeF v (Term.var 0) (Formula.forall a)) :=
  prf_substfc_arith_open v (Term.var 0) (Formula.forall a)

/-- Y anidado: dos binders, o sea `liftc 0 (liftc 0 #0)`. Sigue sin pedir nada. -/
theorem eq_forall_forall_w_es_var0 (v : Nat) (a : Formula) :
    Prf (substfc (numeral v) (Term.var 0)
        (formCode (Formula.forall (Formula.forall a)))
      =eq substCodeF v (Term.var 0) (Formula.forall (Formula.forall a))) :=
  prf_substfc_arith_open v (Term.var 0) (Formula.forall (Formula.forall a))

/-! ## 4 · ⚠️ LO QUE ESTO **NO** DICE

    `prf_substfc_arith_open` es la versión **META**: su `f` es una `Formula` de Lean, no un código
    OBJETO abstracto. `pcc_eval_substfc` sigue haciendo falta y sigue siendo el trabajo grande.

    Lo que estos teoremas SÍ establecen es **estructural y se transfiere**: en las ocho ecuaciones
    de `substfc`, el sustituyendo **nunca se inspecciona** — sólo se traslada (y se `liftc`ea al
    cruzar un binder). La inducción de `pcc_eval_substfc` va sobre el CÓDIGO DE FÓRMULA, con `v` y
    `s` **universalmente cuantificados**; la hipótesis de inducción se aplica a
    `(σv, liftc 0 s, a)` sin pedirle nada a `liftc 0 s`.

    ⇒ **`pcc_eval_liftc` como clausura de `isTermCode` bajo `liftc` NO es un prerrequisito.**
    Lo que falta de ③ es otra cosa: `substfcT` **ni siquiera está definido** (comprobado: 0
    ocurrencias en el árbol), así que ③ empieza por definir el constructor de código dotado
    —como `nthcT`/`lencT`, que son `funcc (strCode …) …` y **no llevan axiomas**— y luego probar
    la ecuación interna por inducción sobre el código, con `pcc_axiom_inst3` sobre las ocho
    `ax_substfc_*` para el paso, y el KIT (`pcc_dot_un`/`pcc_dot_bin`) para el ensamblaje. -/

end SustituyendoOpaco

#print axioms SustituyendoOpaco.forall_recurre_en_liftc
#print axioms SustituyendoOpaco.eq_forall_w_abstracto
#print axioms SustituyendoOpaco.eq_forall_w_es_var0
#print axioms SustituyendoOpaco.eq_forall_forall_w_es_var0

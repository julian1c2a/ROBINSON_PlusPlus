/- # `Probe/B3_planos_dedup_funcc3.lean` — ¿donde cabe el KIT TERNARIO del sondeo?

   Arnes 4 de 4 del angulo (B) sobre `sondeos/SubstfcPlanos.lean`.

   ⚠️ **LA LISTA DE `import` DE ESTE FICHERO ES, BYTE A BYTE, LA DE
   `ROBINSON_PlusPlus/Meta/EvalArithPrf.lean`** (cuatro modulos), y los `open` tambien.
   `EvalArithPrf` es donde viven `prf_substtc_funcc1` y `prf_substtc_funcc2`, o sea el sitio
   natural del tercero. Aqui se comprueba que a ese modulo NO le falta ninguna constante para
   alojar el bloque ENTERO de nueve declaraciones ternarias del sondeo:

     `prf_substtc_funcc3`  `prf_congr_funcc3`
     `substfcT`  `substfcT_termCode`  `prf_congr_substfcT`  `prf_substtc_substfcT`
     `substtc_inv_substfcT`  `liftTerm_substfcT`  `substTerm_substfcT`

   Esas nueve son GENUINAMENTE NUEVAS (ningun homonimo ni sinonimo en produccion), y son
   ademas el bloque COMPARTIDO: `sondeos/SubstfcEx.lean` y `sondeos/EvalSubstfcPrf.lean`
   traen las nueve byte a byte, y `sondeos/EvalSubsttc.lean` las dos primeras. Promoverlas
   una vez aqui las quita de los cuatro sondeos a la vez.

   CERO axiomas de Lean nuevos, CERO `sorry`. -/
import ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf
import ROBINSON_PlusPlus.Meta.MpCodePrf
import ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
import ROBINSON_PlusPlus.Meta.NumCodeClosedPrf

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.TcArithPrf
open ROBINSON_PlusPlus.Meta.Sigma1Prf
open ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
open ROBINSON_PlusPlus.Meta.MpCodePrf
open ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf
open ROBINSON_PlusPlus.Meta.NumCodeClosedPrf
open ROBINSON_PlusPlus.Meta.DerivCondPrf
open ROBINSON_PlusPlus.Meta.HilbertDeduction

set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

namespace B3PlanosFuncc3

/-! ## §0 · Lo que `EvalArithPrf` DECLARA sobre el punto de insercion (verbatim, prefijo `E_`).
     `prf_substtc_funcc1`/`_funcc2` son de ese modulo, asi que aqui no llegan por `import`. -/

theorem E_prf_substtc_funcc2 (v W sc x y : Term) :
    Prf (substtc v W (funcc sc (cons x (cons y nil)))
      =eq funcc sc (cons (substtc v W x) (cons (substtc v W y) nil))) :=
  prf_eq_trans (prf_substtc_func v W sc (cons x (cons y nil)))
    (prf_congr_funcc2
      (prf_eq_trans (prf_substtsc_cons v W x (cons y nil))
        (prf_congr_cons_tail
          (prf_eq_trans (prf_substtsc_cons v W y nil)
            (prf_congr_cons_tail (prf_substtsc_nil v W))))))

/-! ## §1 · El KIT TERNARIO del sondeo, ENTERO, con los imports de `EvalArithPrf`.

    Texto copiado del sondeo sin cambiar una coma. Si compila aqui, cabe ahi. -/

theorem prf_substtc_funcc3 (v W sc x y z : Term) :
    Prf (substtc v W (funcc sc (cons x (cons y (cons z nil))))
      =eq funcc sc (cons (substtc v W x) (cons (substtc v W y) (cons (substtc v W z) nil)))) :=
  prf_eq_trans (prf_substtc_func v W sc (cons x (cons y (cons z nil))))
    (prf_congr_funcc2
      (prf_eq_trans (prf_substtsc_cons v W x (cons y (cons z nil)))
        (prf_congr_cons_tail
          (prf_eq_trans (prf_substtsc_cons v W y (cons z nil))
            (prf_congr_cons_tail
              (prf_eq_trans (prf_substtsc_cons v W z nil)
                (prf_congr_cons_tail (prf_substtsc_nil v W))))))))

theorem prf_congr_funcc3 {sc x x' y y' z z' : Term}
    (hx : Prf (x =eq x')) (hy : Prf (y =eq y')) (hz : Prf (z =eq z')) :
    Prf (funcc sc (cons x (cons y (cons z nil)))
      =eq funcc sc (cons x' (cons y' (cons z' nil)))) :=
  prf_congr_funcc2 (prf_eq_trans (prf_congr_cons_head hx)
    (prf_congr_cons_tail (prf_eq_trans (prf_congr_cons_head hy)
      (prf_congr_cons_tail (prf_congr_cons_head hz)))))

def substfcT (v s f : Term) : Term :=
  funcc (strCode "substfc") (cons v (cons s (cons f nil)))

theorem substfcT_termCode (v s f : Term) :
    substfcT (termCode v) (termCode s) (termCode f) = termCode (substfc v s f) := rfl

theorem prf_congr_substfcT {v v' s s' f f' : Term}
    (hv : Prf (v =eq v')) (hs : Prf (s =eq s')) (hf : Prf (f =eq f')) :
    Prf (substfcT v s f =eq substfcT v' s' f') := prf_congr_funcc3 hv hs hf

theorem prf_substtc_substfcT (v W x y z : Term) :
    Prf (substtc v W (substfcT x y z)
      =eq substfcT (substtc v W x) (substtc v W y) (substtc v W z)) :=
  prf_substtc_funcc3 v W (strCode "substfc") x y z

theorem substtc_inv_substfcT {X Y Z : Term}
    (hX : ∀ W, Prf (substtc zero W X =eq X)) (hY : ∀ W, Prf (substtc zero W Y =eq Y))
    (hZ : ∀ W, Prf (substtc zero W Z =eq Z)) :
    ∀ W, Prf (substtc zero W (substfcT X Y Z) =eq substfcT X Y Z) := fun W =>
  prf_eq_trans (prf_substtc_substfcT zero W X Y Z) (prf_congr_substfcT (hX W) (hY W) (hZ W))

theorem liftTerm_substfcT (k : Nat) (v s f : Term) :
    liftTerm k (substfcT v s f) = substfcT (liftTerm k v) (liftTerm k s) (liftTerm k f) := by
  simp only [substfcT, funcc, cons, nil, zero, succ, liftTerm, liftTerms, liftTerm_strCode]

theorem substTerm_substfcT (k : Nat) (u v s f : Term) :
    substTerm k u (substfcT v s f)
      = substfcT (substTerm k u v) (substTerm k u s) (substTerm k u f) := by
  simp only [substfcT, funcc, cons, nil, zero, succ, substTerm, substTerms, substTerm_strCode]

/-! ## §2 · CONTROLES

    (a) `prf_substtc_funcc3` NO es un caso de `prf_substtc_funcc2`: la lista de argumentos
        tiene tres elementos, no dos. El control positivo es que `funcc2` sigue probando lo
        SUYO y no lo del tercero.
    (b) ⚠️ TRAMPA DE NOMBRE que la promocion hereda: en produccion, el `2` de
        `prf_substtc_funcc2` cuenta ARGUMENTOS, pero el `2` de `prf_congr_funcc2` NO —
        ese es la congruencia en la LISTA entera, con la lista como un solo `Term`. El
        `prf_congr_funcc3` del sondeo cuenta ARGUMENTOS. O sea que `prf_congr_funcc2` y
        `prf_congr_funcc3` NO son dos miembros de una misma familia pese al nombre.
        Se compila la diferencia para que quede escrita. -/

example (v W sc x y : Term) :
    Prf (substtc v W (funcc sc (cons x (cons y nil)))
      =eq funcc sc (cons (substtc v W x) (cons (substtc v W y) nil))) :=
  E_prf_substtc_funcc2 v W sc x y

/-- `prf_congr_funcc2` es la congruencia en la LISTA (un argumento `Term`), no en dos
    argumentos: se aplica con UNA hipotesis. -/
example {sc a b : Term} (h : Prf (a =eq b)) : Prf (funcc sc a =eq funcc sc b) :=
  prf_congr_funcc2 h

/-- `prf_congr_funcc3` pide TRES hipotesis, una por argumento. No es el sucesor de la de
    arriba en ninguna familia; el nombre miente. -/
example {sc x x' y y' z z' : Term}
    (hx : Prf (x =eq x')) (hy : Prf (y =eq y')) (hz : Prf (z =eq z')) :
    Prf (funcc sc (cons x (cons y (cons z nil)))
      =eq funcc sc (cons x' (cons y' (cons z' nil)))) := prf_congr_funcc3 hx hy hz

set_option linter.unusedVariables false in
/-- CONTROL NEGATIVO: `substfcT` no es `rfl`-igual a nada del codigo objeto; en particular
    la ecuacion que persigue el frente NO es una reflexividad. -/
example (v s f : Term) : True := by
  fail_if_success exact (rfl : substfcT (tcFn v) (tcFn s) (tcFn f) = tcFn (substfc v s f))
  trivial

end B3PlanosFuncc3

#print axioms B3PlanosFuncc3.prf_substtc_funcc3
#print axioms B3PlanosFuncc3.prf_congr_funcc3
#print axioms B3PlanosFuncc3.substfcT_termCode
#print axioms B3PlanosFuncc3.prf_congr_substfcT
#print axioms B3PlanosFuncc3.prf_substtc_substfcT
#print axioms B3PlanosFuncc3.substtc_inv_substfcT
#print axioms B3PlanosFuncc3.liftTerm_substfcT
#print axioms B3PlanosFuncc3.substTerm_substfcT

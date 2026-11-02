/- ADVERSARIAL: ¿donde pertenecen `prf_substtc_funcc3` / `prf_congr_funcc3`?
   Tesis: NO al modulo del frente (`EvalSubstfcPlanosPrf`), sino AGUAS ARRIBA,
   junto a `funcc1/2`. Import DELIBERADAMENTE ESTRECHO: EvalArithPrf, que es donde
   viven `prf_substtc_funcc1/2`. NO se importa el barrel. -/
import ROBINSON_PlusPlus.Meta.EvalArithPrf

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.NumCodeClosedPrf ROBINSON_PlusPlus.Meta.EvalArithPrf

namespace ZZAdvFuncc3

-- copia LITERAL de sondeos/SubstfcPlanos.lean:38 (= sondeos/EvalSubsttc.lean:78, identica)
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

-- copia LITERAL de sondeos/SubstfcPlanos.lean:50
theorem prf_congr_funcc3 {sc x x' y y' z z' : Term}
    (hx : Prf (x =eq x')) (hy : Prf (y =eq y')) (hz : Prf (z =eq z')) :
    Prf (funcc sc (cons x (cons y (cons z nil)))
      =eq funcc sc (cons x' (cons y' (cons z' nil)))) :=
  prf_congr_funcc2 (prf_congr_cons_head hx |> fun h =>
    prf_eq_trans h (prf_congr_cons_tail (prf_eq_trans (prf_congr_cons_head hy)
      (prf_congr_cons_tail (prf_congr_cons_head hz)))))

#print axioms prf_substtc_funcc3
#print axioms prf_congr_funcc3

end ZZAdvFuncc3

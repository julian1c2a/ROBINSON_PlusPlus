import ROBINSON_PlusPlus.Meta

/-! VERIFICADOR ADVERSARIAL — DUPLICADO NO DECLARADO en el bloque §9 de B2.

    `Meta/LiftcCodePrf.lean:752,757` (PROMOVIDO AYER, el mismo fichero contra el que el
    preparador dice haber deduplicado) ya contiene:

        refl_termCode  : ∀ t  : Term,      Prf (targetLift   (termCode  t))
        refl_termsCode : ∀ ts : List Term, Prf (targetLiftsc (termsCode ts))

    y `Meta/Representability.lean:158,161` contiene los puentes
    `termCodeM_eq` / `termsCodeM_eq`. Juntos DAN YA, en produccion, los enunciados de
    SEIS de los nueve controles §9 de B2. -/

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.Representability
open ROBINSON_PlusPlus.Meta.LiftcCodePrf

namespace ADV_V3

/-! ## (1) El enunciado de `CRIT_targetLift_real` ya es un teorema de produccion. -/
theorem CRIT_targetLift_real_YA (t : Term) : Prf (targetLift (termCodeM t)) :=
  (termCodeM_eq t) ▸ refl_termCode t

/-! ## (2) El enunciado de `CRIT_targetLiftsc_real` tambien.
    ⚠️ Notese que el `f : String` del enunciado de B2 NO APARECE en el tipo: el control es,
    literalmente, `∀ ts, Prf (targetLiftsc (termsCodeM ts))` = `refl_termsCode` + puente. -/
theorem CRIT_targetLiftsc_real_YA (f : String) (ts : List Term) :
    Prf (targetLiftsc (termsCodeM ts)) :=
  (termsCodeM_eq ts) ▸ refl_termsCode ts

/-! ## (3) `CRIT_real_A`, `CRIT_real_B`, `CRIT_real_lista` son instancias suyas. -/
def tEjA : Term := succ (Term.var 0)
def tEjB : Term := add (succ (Term.var 0)) (Term.var 1)

theorem CRIT_real_A_YA : Prf (targetLift (termCodeM tEjA)) := CRIT_targetLift_real_YA tEjA
theorem CRIT_real_B_YA : Prf (targetLift (termCodeM tEjB)) := CRIT_targetLift_real_YA tEjB
theorem CRIT_real_lista_YA :
    Prf (targetLiftsc (termsCodeM [succ (Term.var 0), Term.var 1])) :=
  CRIT_targetLiftsc_real_YA add_sym _

/-! ## (4) Y `CRIT_hasWit_descenso` tiene EL MISMO TIPO que `CRIT_targetLift_real`
    (duplicado INTERNO del propio modulo B2, tambien sin declarar). -/
theorem CRIT_hasWit_descenso_YA (t : Term) : Prf (targetLift (termCodeM t)) :=
  CRIT_targetLift_real_YA t

/-! ## CONTROL DE QUE NO ME ENGANO: los tipos son LOS MISMOS, comprobado por `rfl` de
    PROPOSICIONES (no de pruebas: `Prf` es `Prop` y la irrelevancia haria pasar cualquier cosa). -/
theorem tipos_iguales_1 (t : Term) :
    Prf (targetLift (termCodeM t)) = Prf (targetLift (termCode t)) := by
  rw [termCodeM_eq]

theorem tipos_iguales_2 (ts : List Term) :
    Prf (targetLiftsc (termsCodeM ts)) = Prf (targetLiftsc (termsCode ts)) := by
  rw [termsCodeM_eq]

/-! ## CONTROL NEGATIVO DURO: `termCodeM` y `termCode` NO son la misma constante, y el
    puente NO es `rfl` — luego esto no es una trivialidad de notacion, es un puente REAL
    (y aun asi el enunciado ya estaba probado). -/
example : True := by
  fail_if_success exact (rfl : @termCodeM = @termCode)
  trivial

example : True := by
  fail_if_success exact (rfl : termCodeM (Term.var 0) = termCode (Term.var 0))
  trivial

/-! ## CONTROL NEGATIVO 2: `refl_termCode` NO es vacuo por si mismo tampoco — pero eso ya
    lo media produccion. Aqui solo mido que las dos rutas coinciden en ENUNCIADO. -/

end ADV_V3

#print axioms ADV_V3.CRIT_targetLift_real_YA
#print axioms ADV_V3.CRIT_targetLiftsc_real_YA
#print axioms ADV_V3.CRIT_real_B_YA
#print axioms ADV_V3.CRIT_real_lista_YA
#print axioms ADV_V3.CRIT_hasWit_descenso_YA

#check @ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_termCode
#check @ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_termsCode
#check @ROBINSON_PlusPlus.Meta.Representability.termCodeM_eq

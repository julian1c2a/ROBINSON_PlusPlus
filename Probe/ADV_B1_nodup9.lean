/-
ADV_B1_nodup9 (v2) — ¿es `substTerm_termCode` del sondeo un DUPLICADO de
`Minimal.Axioms.substTerm_termCodeM` de PRODUCCION? (el agente NO lo declaro duplicado).

v1 fallo por usar LITERALES cerrados: `numeral 3` y `numeralM 3` SI reducen al mismo termino.
La pregunta real es a nivel de FUNCION / de VARIABLE.
-/
import ROBINSON_PlusPlus.Meta

open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.ReprPrf

namespace AdvNoDup9

/-- (a) Con LITERAL cerrado si coinciden — esto NO decide nada. -/
theorem literal_si_coincide : numeral 3 = numeralM 3 := rfl

/-- (b) A nivel de FUNCION: ¿son la misma? Si esto compilase, serian intercambiables. -/
example : True := by
  fail_if_success have _ : @numeral = @numeralM := rfl
  trivial

example : True := by
  fail_if_success have _ : @termCode = @termCodeM := rfl
  trivial

/-- (c) Con VARIABLE libre (el caso que importa para un lema generico). -/
example (k : Nat) : True := by
  fail_if_success have _ : numeral k = numeralM k := rfl
  trivial

example (t : Term) : True := by
  fail_if_success have _ : termCode t = termCodeM t := rfl
  trivial

/-- (d) El ENUNCIADO ENTERO de los dos lemas: ¿el mismo tipo? -/
example : True := by
  fail_if_success
    have _ : (∀ (v : Nat) (u : Term) (t : Term), substTerm v u (termCode t) = termCode t)
           = (∀ (v : Nat) (s : Term) (t : Term), substTerm v s (termCodeM t) = termCodeM t) := rfl
  trivial

end AdvNoDup9

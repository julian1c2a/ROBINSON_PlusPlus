import ROBINSON_PlusPlus.Meta
/-! CONTROL del verificador: SIN el `export` colisionante, `refl_lista_nil` a secas SI resuelve.
    Si esto compila, el `fail_if_success` del §G de `B3_substtc_dedup.lean` NO es vacuo. -/
open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Hilbert
example : True := by
  have := refl_lista_nil
  trivial
example : True := by
  have := refl_caso_varc
  trivial
example : True := by
  have := PSI_inst
  trivial

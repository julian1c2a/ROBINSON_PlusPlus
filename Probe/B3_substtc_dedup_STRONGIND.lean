/-
# ANEXO de `Probe/B3_substtc_dedup.lean` — la comprobacion ADR-019.

`psi_l1` / `psi_l2` / `psi_l3` / `PSI3` / `PSI_inst` se copian LETRA POR LETRA (modulo `Φ`) en
CINCO sondeos: `EvalSubsttc`, `EvalSubstfcPrf`, `EnsamblajeTriple`, `EnsamblajeMedida` y
`HasWitFReal`. `psi_l1` YA es `StrongInductionPrf.psi_lift_form` instanciado (ver §C.2 del
fichero principal); las otras tres no existen en produccion.

Este anexo comprueba que la version GENERAL —cuantificada en `Φ`— se prueba **con lo que ya hay
al llegar a `Meta/StrongInductionPrf.lean`**: el unico `import` es ese modulo, ni el barrel
`ROBINSON_PlusPlus.Meta` ni nada aguas abajo. Si compila, los tres lemas pueden anadirse al
FINAL de `StrongInductionPrf.lean` sin tocar su cabecera de imports, que es lo que exige
ADR-019 («hay que BAJAR el general»).

    lake env lean Probe/B3_substtc_dedup_STRONGIND.lean
-/
import ROBINSON_PlusPlus.Meta.StrongInductionPrf

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.StrongInductionPrf
open FOL

set_option linter.unusedSimpArgs false

namespace ANEXO_STRONGIND

/-- `psi_lift_form` a DOS niveles. Version general de `psi_l2` (5 copias en `sondeos/`). -/
theorem psi_lift_form2 (Φ : Formula) (hΦ : liftFormula 1 Φ = Φ) :
    liftFormula 0 (liftFormula 0 (PSI Φ))
      = Formula.forall (Formula.impl (lt (.var 0) (.var 3)) Φ) := by
  rw [psi_lift_form Φ hΦ]
  simp only [lt, liftFormula, liftTerm, liftTerms, Nat.reduceAdd, Nat.reduceLT, reduceIte, hΦ]

/-- `psi_lift_form` a TRES niveles. Version general de `psi_l3` (5 copias en `sondeos/`). -/
theorem psi_lift_form3 (Φ : Formula) (hΦ : liftFormula 1 Φ = Φ) :
    liftFormula 0 (liftFormula 0 (liftFormula 0 (PSI Φ)))
      = Formula.forall (Formula.impl (lt (.var 0) (.var 4)) Φ) := by
  rw [psi_lift_form2 Φ hΦ]
  simp only [lt, liftFormula, liftTerm, liftTerms, Nat.reduceAdd, Nat.reduceLT, reduceIte, hΦ]

/-- Version general de `PSI_inst` a profundidad 3 (la que usan los descensos con TRES
    parametros cuantificados dentro del predicado). Espeja a `StrongInductionPrf.PSI_inst`,
    que es la de profundidad 1. -/
theorem PSI_inst3 (Φ : Formula) (hΦ : liftFormula 1 Φ = Φ) {Γ : List Formula}
    (hpsi : PrfH Γ (liftFormula 0 (liftFormula 0 (liftFormula 0 (PSI Φ))))) (z : Term) :
    PrfH Γ (Formula.impl (lt z (.var 3)) (substFormula 0 z Φ)) := by
  rw [psi_lift_form3 Φ hΦ] at hpsi
  have h := PrfH_spec hpsi z
  have e : substFormula 0 z (Formula.impl (lt (.var 0) (.var 4)) Φ)
      = Formula.impl (lt z (.var 3)) (substFormula 0 z Φ) := by
    simp only [substFormula, lt, substTerm, substTerms, Nat.reduceEqDiff, Nat.reduceGT,
      Nat.reduceSub, reduceIte, if_true]
  rwa [e] at h

end ANEXO_STRONGIND

#print axioms ANEXO_STRONGIND.psi_lift_form2
#print axioms ANEXO_STRONGIND.psi_lift_form3
#print axioms ANEXO_STRONGIND.PSI_inst3

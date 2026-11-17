/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.GodelTwoPrf
import ROBINSON_PlusPlus.Meta.Sentencia
-- (2026‑10‑19, T74: el único `import` de los módulos de FOL sin nada en el cono que se queda. Lo piden
-- `diagBeta_lift1`, `liar_isSentence` y, en `Meta/Rosser.lean`, `R_isSentence`, que reescriben con
-- `FOL.Lift0.liftFormula_subst` y `FOL.Lift0.liftFormula_lift`; las tres están FUERA del cono de los titulares.)
import FOL.Lift0

/-!
# `Meta/TarskiPrf.lean` — 🏁 TARSKI: la verdad no es definible en la teoría (ADR‑121)

✏️ 2026‑11‑17 (ADR‑268, las capas de B1): `tarski` está en `Meta/TitularesII.lean`; `tarski_semantico` y `tarski_semantico_de`, en `Meta/TitularesIII.lean`; `IsSentence` y `godelCN_isSentence`, en `Meta/Sentencia.lean`. Aquí queda la parte de la clase (i), sin la semántica.

* `prf_diagonal (P)` — **el lema diagonal para un predicado ARBITRARIO**: `selfAppN (diagBeta P)` es punto fijo de
  `P`. La composición de sustituciones que hacía falta es una línea de FOL, `FOL.subst_subst_lift_gen`, con la
  plantilla `diagBeta P := substFormula 0 diagTerm (liftFormula 1 P)` (el mismo patrón «lift‑aware» que la
  inducción). Hasta hoy el punto fijo de fórmula sólo existía para `godelPred'`. Es también la pieza que Rosser
  necesita.
* `liar Tr` — el mentiroso de `Tr`, y `prf_liar`: `Prf (L ⇔ ¬ Tr(⌜L⌝))`.
* `prf_tarski (Tr)` — **sin hipótesis**: la teoría REFUTA `Tr(⌜L⌝) ⇔ L` en el mentiroso `L`, para todo `Tr`.
* `tarski (Tr)` — **sin hipótesis** (`consistencia`, ADR‑120): `Tr(⌜L⌝) ⇔ L` NO es teorema: ninguna `Tr` define la
  verdad en la teoría, y falla en su propio mentiroso, que es una sentencia (`liar_isSentence`) del lenguaje de
  `Tr` y de la aritmética. ⚠️ No se enuncia la forma «para toda `φ`»: una fórmula abierta o un símbolo ajeno la
  refutan sin mentiroso (§4).
* `godelCN_isSentence` — la sentencia de Gödel también es una sentencia, por la misma vía que `liar_isSentence` (T12,
  ADR‑187).
* `tarski_semantico_de (hM) (Tr) (v)` — **Tarski semántico**: tampoco en un modelo estándar CUALQUIERA (`Estandar M`,
  T75a, ADR‑175); `tarski_semantico (Tr) (v)` es su instancia en `MNV V₀`, **Tarski en ℕ**.

Las pruebas que tocan el numeral `numeral (codeNat …)` van por `Eq.mpr` con motivo explícito y lemas universales:
ninguna le pide a una táctica ni al núcleo evaluar el numeral (ADR‑117 §3).

`prf_diagonal` y `prf_tarski` no usan el predicado de demostrabilidad, ni D1–D3, ni el ancla; `tarski` y
`tarski_semantico` sí usan el modelo (por `consistencia` y la solidez), y con él el ancla; `tarski_semantico_de`, la
solidez de un `M` estándar cualquiera.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open FOL ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.HilbertDeduction ROBINSON_PlusPlus.Meta.Diagonal
open ROBINSON_PlusPlus.Meta.DiagonalNumeral ROBINSON_PlusPlus.Meta.GodelTwoPrf ROBINSON_PlusPlus.Meta.Sentencia

namespace ROBINSON_PlusPlus.Meta.TarskiPrf

/-! ## §1 · El lema diagonal para un predicado ARBITRARIO (`liftFormula 1`: la composición, sin hipótesis) -/
def diagBeta (P : Formula) : Formula := substFormula 0 diagTerm (liftFormula 1 P)

theorem diagBeta_comp (P : Formula) (s : Term) :
    substFormula 0 s (diagBeta P) = substFormula 0 (substTerm 0 s diagTerm) P :=
  FOL.subst_subst_lift_gen P s diagTerm 0

theorem prf_diagonal (P : Formula) :
    Prf (selfAppN (diagBeta P) ⇔ substFormula 0 (numeral (codeNat (selfAppN (diagBeta P)))) P) :=
  Eq.mpr
    (congrArg (fun X => Prf (X ⇔ substFormula 0 (numeral (codeNat (selfAppN (diagBeta P)))) P))
      (diagBeta_comp P (numeral (codeNat (diagBeta P)))))
    (prf_subst_eq_iff P (prf_diag_arith_num (diagBeta P)))

/-! ## §2 · El mentiroso -/
theorem substFormula_neg (v : Nat) (s : Term) (A : Formula) :
    substFormula v s (neg A) = neg (substFormula v s A) := rfl

noncomputable def liar (Tr : Formula) : Formula := selfAppN (diagBeta (neg Tr))

theorem prf_liar (Tr : Formula) :
    Prf (liar Tr ⇔ neg (substFormula 0 (numeral (codeNat (liar Tr))) Tr)) :=
  Eq.mpr (congrArg (fun X => Prf (liar Tr ⇔ X))
      (substFormula_neg 0 (numeral (codeNat (liar Tr))) Tr).symm)
    (prf_diagonal (neg Tr))

/-! ## §3 · El núcleo proposicional (intuicionista), con `T` y `L` ABSTRACTOS: el numeral no entra -/
theorem prf_neg_iff_of_iff_neg {T L : Formula} (fp : Prf (L ⇔ neg T)) : Prf (neg (T ⇔ L)) := by
  apply prf_deduction
  have hH : PrfH [T ⇔ L] (T ⇔ L) := prfH_hyp_self _
  have hTL : PrfH [T ⇔ L] (T ⇒ L) := PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prfᵢ.c2 (T ⇒ L) (L ⇒ T))) hH
  have hLT : PrfH [T ⇔ L] (L ⇒ T) := PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prfᵢ.c3 (T ⇒ L) (L ⇒ T))) hH
  have hLnT : PrfH [T ⇔ L] (L ⇒ neg T) := prf_to_prfH (prf_and_elim_left fp) _
  have hnTL : PrfH [T ⇔ L] (neg T ⇒ L) := prf_to_prfH (prf_and_elim_right fp) _
  have hnL : PrfH [T ⇔ L] (L ⇒ ⊥) := prfH_s_app hLnT hLT
  have hnT : PrfH [T ⇔ L] (T ⇒ ⊥) := prfH_s_app (prfH_weaken hnL) hTL
  exact PrfH.mp _ _ _ hnL (PrfH.mp _ _ _ hnTL hnT)

/-! ## §4 · TARSKI, sintáctico: `Tr` falla en su propio MENTIROSO

La forma fiel: dada `Tr`, el contraejemplo es su mentiroso `L := liar Tr`, una SENTENCIA (`liar_isSentence`, §5)
hecha sólo con `Tr` y la maquinaria de la aritmética. ⚠️ La forma «no hay `Tr` con `Prf (Tr(⌜φ⌝) ⇔ φ)` para TODA
`φ`» sería verdadera pero barata: una fórmula ABIERTA (`#0 =eq zero`) o un símbolo ajeno al lenguaje la refutan sin
ningún mentiroso (lo señaló la auditoría adversarial del 2026‑10‑05, `wf_68cece92-90b`). Por eso no se enuncia. -/

/-- Para toda `Tr`, la teoría REFUTA `Tr(⌜L⌝) ⇔ L` en el mentiroso. Sin hipótesis. -/
theorem prf_tarski (Tr : Formula) :
    Prf (neg (substFormula 0 (numeral (codeNat (liar Tr))) Tr ⇔ liar Tr)) :=
  prf_neg_iff_of_iff_neg (prf_liar Tr)

/-! ## §5 · El mentiroso es una SENTENCIA (la invariancia por lift, la noción de `axioms_lift_eq`) -/
theorem liftFormula_neg (c : Nat) (A : Formula) :
    liftFormula c (neg A) = neg (liftFormula c A) := rfl
theorem diagBeta_lift1 {P : Formula} (hP : liftFormula 1 P = P) :
    liftFormula 1 (diagBeta P) = diagBeta P := by
  rw [diagBeta, FOL.Lift0.liftFormula_subst _ 0 1 (Nat.zero_le 1), liftTerm_one_diagTerm,
    ← FOL.Lift0.liftFormula_lift P 1 1 (Nat.le_refl 1), hP, hP]

/-- Si `Tr` tiene a lo sumo `#0` libre (`liftFormula 1 Tr = Tr`), su mentiroso es una sentencia. -/
theorem liar_isSentence {Tr : Formula} (hTr : liftFormula 1 Tr = Tr) : IsSentence (liar Tr) := by
  have hβ : liftFormula (0 + 1) (diagBeta (neg Tr)) = diagBeta (neg Tr) :=
    diagBeta_lift1 (by rw [liftFormula_neg, hTr])
  show liftFormula 0 (substFormula 0 (numeral (codeNat (diagBeta (neg Tr)))) (diagBeta (neg Tr)))
     = substFormula 0 (numeral (codeNat (diagBeta (neg Tr)))) (diagBeta (neg Tr))
  rw [FOL.Lift0.liftFormula_subst _ 0 0 (Nat.le_refl 0),
    ROBINSON_PlusPlus.Meta.DerivCondPrf.liftTerm_numeral, hβ]

/-! ## §6 · Control negativo: con `Prf ⊥`, el bicondicional del mentiroso SÍ sería teorema (la consistencia no
sobra) -/
example (hbot : Prf Formula.bottom) (Tr : Formula) :
    Prf (substFormula 0 (numeral (codeNat (liar Tr))) Tr ⇔ liar Tr) :=
  prf_mp (Prf.incl (Prfᵢ.efq _)) hbot

end ROBINSON_PlusPlus.Meta.TarskiPrf

#print axioms ROBINSON_PlusPlus.Meta.TarskiPrf.prf_diagonal
#print axioms ROBINSON_PlusPlus.Meta.TarskiPrf.prf_tarski

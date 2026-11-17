/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.DiagonalNumeral
import ROBINSON_PlusPlus.Meta.DerivCondPrf
import FOL.Lift0

/-!
# `Meta/Sentencia.lean` — qué es una SENTENCIA, y que `G` lo es (C3; ADR‑268)

`IsSentence φ` (`liftFormula 0 φ = φ`: `φ` no tiene variables libres) y `godelCN_isSentence` (T12, ADR‑187), con los
lemas de lift de `godelPred'` y `godelBeta'` que la prueban. Vivían en `Meta/TarskiPrf.lean` (C7.i); bajan a la capa
del punto fijo (C3 de ADR‑266) porque los usan el enunciado de `rosser_ext`, el puente con FOL (C6, que los importaba
de `TarskiPrf`: hacia arriba, el nudo N5 de ADR‑266) y Tarski. Mismos enunciados y pruebas; cambia el espacio de
nombres, que es el de este fichero (NAMING‑CONVENTIONS §6).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open FOL ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.Diagonal ROBINSON_PlusPlus.Meta.DiagonalNumeral ROBINSON_PlusPlus.Meta.DiagonalTwo
open ROBINSON_PlusPlus.Meta.ProofChain

namespace ROBINSON_PlusPlus.Meta.Sentencia

def IsSentence (φ : Formula) : Prop := liftFormula 0 φ = φ

theorem liftTerm_one_diagTerm : liftTerm 1 diagTerm = diagTerm := rfl


/-- `godelPred' = ¬ provFormulaC'` tiene a lo sumo `#0` libre. -/
theorem godelPred'_lift2 : liftFormula 2 godelPred' = godelPred' := by
  simp only [godelPred', neg, provFormulaC', liftFormula, liftTerm, liftTerms, land, chainOk, In, runFn, nil, zero,
    Nat.reduceAdd, Nat.reduceLT, reduceIte]

theorem godelBeta'_lift1 : liftFormula (0 + 1) godelBeta' = godelBeta' := by
  unfold godelBeta'
  rw [FOL.Lift0.liftFormula_subst _ 0 1 (Nat.zero_le 1), liftTerm_one_diagTerm, godelPred'_lift2]

/-- 🏁 **La sentencia de Gödel es una SENTENCIA** (T12, ADR‑187): la gemela de `liar_isSentence` para `godelCN`. Por
    `unfold` y `rw` con lemas universales: el numeral `numeral (codeNat godelBeta')` no se evalúa nunca. -/
theorem godelCN_isSentence : IsSentence godelCN := by
  unfold IsSentence godelCN selfAppN
  rw [FOL.Lift0.liftFormula_subst _ 0 0 (Nat.le_refl 0),
    ROBINSON_PlusPlus.Meta.DerivCondPrf.liftTerm_numeral, godelBeta'_lift1]

end ROBINSON_PlusPlus.Meta.Sentencia

#print axioms ROBINSON_PlusPlus.Meta.Sentencia.godelCN_isSentence

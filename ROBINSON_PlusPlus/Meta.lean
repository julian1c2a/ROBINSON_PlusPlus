/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT

Barrel file for `Meta/` — Gödelización del sistema `Minimal`.
Public API:
  · Godel          (Nivel B): G, ⌜·⌝, Teo G1 (encode_injective)
  · Provability    (Nivel C): formCode, IsFormula, Provable, Dem, diagonal_lemma,
                              goedelSentence
  · Incompleteness (Nivel D): goedel_first_unprovable, goedel_first_true,
                              incompleteness (Primer Teorema, mitad esencial)
-/
import ROBINSON_PlusPlus.Meta.Godel
import ROBINSON_PlusPlus.Meta.Provability
import ROBINSON_PlusPlus.Meta.Incompleteness
import ROBINSON_PlusPlus.Meta.Hilbert
import ROBINSON_PlusPlus.Meta.HilbertSeq
import ROBINSON_PlusPlus.Meta.CodeArith
import ROBINSON_PlusPlus.Meta.SubstArith
import ROBINSON_PlusPlus.Meta.StepArith
import ROBINSON_PlusPlus.Meta.CheckArith
import ROBINSON_PlusPlus.Meta.Representability
import ROBINSON_PlusPlus.Meta.Necessitation
import ROBINSON_PlusPlus.Meta.Diagonal
import ROBINSON_PlusPlus.Meta.CodeDistinct
import ROBINSON_PlusPlus.Meta.Induction
import ROBINSON_PlusPlus.Meta.ProofChain
import ROBINSON_PlusPlus.Meta.DerivCond
import ROBINSON_PlusPlus.Meta.Representability2
import ROBINSON_PlusPlus.Meta.Reflection
import ROBINSON_PlusPlus.Meta.GodelTwo

import Lake
open Lake DSL

-- The name of the project, must match the directory name.
package «ROBINSON_PlusPlus» where
  -- `autoImplicit` desactivado en el EDITOR y en `lake build` (ADR‑128 de RPP, 2026‑10‑05). Antes era
  -- `moreServerArgs := #["-DautoImplicit=false"]`, que sólo llega al servidor del editor: `lake build`
  -- aceptaba variables implícitas automáticas (medido con un módulo sonda). `leanOptions` vale para los
  -- dos; activarlo no rompió ningún módulo (build completo desde cero, medido).
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

-- ── External dependencies ────────────────────────────────────────────────────

-- FOL: First-Order Logic with Equality (local sibling project)
-- Provides: Term, Formula, Derives (⊢), substitution, equality rules, tactics
require FOL from "../FOL"

-- ZfcSetTheory: ZFC set theory in Lean 4, no Mathlib
-- require ZfcSetTheory from git
--   "https://github.com/julian1c2a/ZfcSetTheory" @ "master"

-- PeanoNatLib: Peano natural numbers, no Mathlib
-- require peanolib from git
--   "https://github.com/julian1c2a/Peano" @ "master"

-- ─────────────────────────────────────────────────────────────────────────────

@[default_target]
lean_lib «ROBINSON_PlusPlus» where

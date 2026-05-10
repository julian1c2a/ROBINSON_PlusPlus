import Lake
open Lake DSL

-- The name of the project, must match the directory name.
package «ROBINSON_PlusPlus» where
  -- Disable auto-implicit to enforce explicit type annotations everywhere
  moreServerArgs := #["-DautoImplicit=false"]

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

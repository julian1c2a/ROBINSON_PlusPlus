import Lake
open Lake DSL

-- The name of the project, must match the directory name.
package «ROBINSON_PlusPlus» where
  -- Disable auto-implicit to enforce explicit type annotations everywhere
  moreServerArgs := #["-DautoImplicit=false"]

-- ── External dependencies (uncomment as needed) ──────────────────────────────

-- ZfcSetTheory: ZFC set theory in Lean 4, no Mathlib
-- Provides: SetUniverse, ExistsUnique, all ZFC axioms + constructions
-- require ZfcSetTheory from git
--   "https://github.com/julian1c2a/ZfcSetTheory" @ "master"

-- PeanoNatLib: Peano natural numbers, no Mathlib
-- Provides: Peano.ℕ₀, Peano.Add, Peano.Mul, Peano.StrictOrder, ...
-- require peanolib from git
--   "https://github.com/julian1c2a/Peano" @ "master"

-- ─────────────────────────────────────────────────────────────────────────────

@[default_target]
lean_lib «ROBINSON_PlusPlus» where

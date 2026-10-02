/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT

Root barrel file for the ROBINSON_PlusPlus library.
Imports all public modules so that `import ROBINSON_PlusPlus` suffices.
-/

-- Lenguaje y axiomas del sistema aritmético Minimal
import ROBINSON_PlusPlus.Minimal.Axioms

-- Meta: Gödelización (Nivel B codificación + Nivel C demostrabilidad). Ver GODEL-STATUS.md
import ROBINSON_PlusPlus.Meta

-- Full: Induction (`inductionFormula`, `primAxioms`, el censo, lemas de sustitución), Numerals
-- (`numeral`) y PrimeFactor (teoría de números META pura ℕ, sin Mathlib: IsPrimeNat, factor
-- primo, factorización). La inducción de la cadena es el constructor `Prf.ind` (Meta/Hilbert.lean).
import ROBINSON_PlusPlus.Full.Induction
import ROBINSON_PlusPlus.Full.Numerals
import ROBINSON_PlusPlus.Full.PrimeFactor
-- FOL: los ocho módulos de FOL que importaban los módulos retirados con ADR‑115.
import FOL.Deduction
import FOL.FOL
import FOL.Tactics
import FOL.Theorems.Derived
import FOL.Theorems.Eq
import FOL.Theorems.Impl
import FOL.Theorems.Neg
import FOL.Theorems.Quantifiers

-- 🗑️ Registro (ADR‑115, 2026‑10‑02): con la capa `⊢` se retiraron, y salieron de este barril,
-- Minimal/Theorems/Block1–8 (diez ficheros: los bloques de teoremas I–VIII) y, de Full, Mod2,
-- Lists, StrongInduction, Bounded, Divisibility, Primality, Division y Factorization. Todo lo que
-- sus comentarios anunciaban —axiomas «derivados como teoremas», inducción fuerte, homomorfismos
-- de numerales, divisibilidad, primalidad, TFA objeto— vivía sobre `⊢` y ya no existe; Lists
-- traía además el `axiom` `ax_list_induction`, que daba `axioms ⊢ ⊥`. Lo retirado de Meta, en su
-- barril (Meta.lean). (Intermediate/, el caso particular con Φ finito, se eliminó el 2026-06-11.)

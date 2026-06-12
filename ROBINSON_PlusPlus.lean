/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT

Root barrel file for the ROBINSON_PlusPlus library.
Imports all public modules so that `import ROBINSON_PlusPlus` suffices.
-/

-- Lenguaje y axiomas del sistema aritmético Minimal
import ROBINSON_PlusPlus.Minimal.Axioms

-- Bloques de teoremas (I–VIII) sobre el sistema Minimal
import ROBINSON_PlusPlus.Minimal.Theorems.Block1
import ROBINSON_PlusPlus.Minimal.Theorems.Block2
import ROBINSON_PlusPlus.Minimal.Theorems.Block3
import ROBINSON_PlusPlus.Minimal.Theorems.Block4
import ROBINSON_PlusPlus.Minimal.Theorems.Block4_C5
import ROBINSON_PlusPlus.Minimal.Theorems.Block4_C6_C7
import ROBINSON_PlusPlus.Minimal.Theorems.Block5
import ROBINSON_PlusPlus.Minimal.Theorems.Block6
import ROBINSON_PlusPlus.Minimal.Theorems.Block7
import ROBINSON_PlusPlus.Minimal.Theorems.Block8

-- Meta: Gödelización (Nivel B codificación + Nivel C demostrabilidad). Ver GODEL-STATUS.md
import ROBINSON_PlusPlus.Meta

-- Intermediate/ ELIMINADO 2026-06-11: el sistema con Φ finito es el caso particular
-- de Full/ con inducción general. Toda la inducción vive ahora en Full/Induction.lean.

-- Full: inducción general object-level (lift-aware). Axiomas algebraicos (ax6-ax12)
-- y de orden (ax18, ax19) derivados como teoremas. Ver NEXT-STEPS Eje 4.
import ROBINSON_PlusPlus.Full.Induction

-- Full: mod2 — ax21 (mod2_range) y ax24 (mod2_of_even) derivados vía
-- ax_mod2_alternation (Opción C.2, 2026-06-11).
import ROBINSON_PlusPlus.Full.Mod2

-- Full: listas — ax_C3 (concat_assoc) y ax_L3 (in_concat) derivados vía
-- meta-axioma ax_list_induction (2026-06-11).
import ROBINSON_PlusPlus.Full.Lists

-- Full: inducción fuerte (course-of-values) DERIVADA de ax_induction
-- (sin axioma nuevo). Base para Ax-P (TFA). Ver NEXT-STEPS Eje 4 F1.
import ROBINSON_PlusPlus.Full.StrongInduction

-- Full: numerales — puente meta↔object (numeral : ℕ → Term) + homomorfismo
-- de +, ·, <. Cimiento de la representabilidad (camino Gödel-aware a TFA).
import ROBINSON_PlusPlus.Full.Numerals

-- Full: cuantificación acotada — le_numeral_split (d ≤ numeral n ⇒ casos finitos).
import ROBINSON_PlusPlus.Full.Bounded

-- Full: divisibilidad representada — numeral_dvd + divisor_le.
import ROBINSON_PlusPlus.Full.Divisibility

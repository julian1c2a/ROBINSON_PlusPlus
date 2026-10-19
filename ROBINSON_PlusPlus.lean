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
-- (✏️ 2026‑10‑14, ADR‑134: hoy también el Nivel D sobre `Prf` —D1–D3, el modelo `MNV V₀`, `consistencia`,
-- Gödel I entero y Gödel II sin hipótesis, Tarski—; GODEL-STATUS.md es histórico salvo su banner: el estado vivo, en
-- NEXT-STEPS.md y AXIOMS.md §0.)
import ROBINSON_PlusPlus.Meta

-- Full: Induction (`inductionFormula`, `primAxioms`, el censo, lemas de sustitución) y Numerals
-- (`numeral`). (✏️ 2026‑10‑18, ADR‑161: PrimeFactor, la teoría de números META pura sobre ℕ, salió del build: nada
-- suyo estaba en el cono de los titulares.) La inducción de la cadena entra por los constructores `Prf.ind` y
-- `Prf.listInd` (Meta/Hilbert.lean; ✏️ 2026‑10‑14: decía «es el constructor `Prf.ind`»; AXIOMS.md §0.3).
import ROBINSON_PlusPlus.Full.Induction
import ROBINSON_PlusPlus.Full.Numerals
-- FOL: los tres módulos de FOL con algo en el cono de los titulares que la librería nombra. (✏️ 2026‑10‑19,
-- ADR‑170, T74: eran ocho, los que importaban los módulos retirados con ADR‑115; `FOL.Deduction`, `FOL.Tactics` y
-- `FOL.Theorems.Derived`, `Impl` y `Neg` no tenían nada en el cono, y salieron de aquí y de los módulos que los
-- importaban. `FOL.Semantics` y `FOL.Lift0` entran por los módulos que los usan; `FOL.Tactics` y los tres
-- `Theorems.*`, por `FOL.Theorems.Quantifiers`.)
import FOL.FOL
import FOL.Theorems.Eq
import FOL.Theorems.Quantifiers

-- 🗑️ Registro (ADR‑115, 2026‑10‑02): con la capa `⊢` se retiraron, y salieron de este barril,
-- Minimal/Theorems/Block1–8 (diez ficheros: los bloques de teoremas I–VIII) y, de Full, Mod2,
-- Lists, StrongInduction, Bounded, Divisibility, Primality, Division y Factorization. Todo lo que
-- sus comentarios anunciaban —axiomas «derivados como teoremas», inducción fuerte, homomorfismos
-- de numerales, divisibilidad, primalidad, TFA objeto— vivía sobre `⊢` y ya no existe; Lists
-- traía además el `axiom` `ax_list_induction`, que daba `axioms ⊢ ⊥`. Lo retirado de Meta, en su
-- barril (Meta.lean). (Intermediate/, el caso particular con Φ finito, se eliminó el 2026-06-11.)

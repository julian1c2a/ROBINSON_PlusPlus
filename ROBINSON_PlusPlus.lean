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

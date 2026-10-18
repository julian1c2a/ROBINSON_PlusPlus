/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.ContratoTitulares

/-!
# `scripts/ContratoGenerar.lean` — regenera la tabla del contrato de los titulares (T07, ADR‑165)

Uso, desde la raíz de RPP y con el build al día: `lake env lean scripts/ContratoGenerar.lean`. Escribe
`ROBINSON_PlusPlus/Meta/ContratoTabla.lean`. ⛔ Sólo tras un ADR que diga qué cambió en el enunciado de qué titular, o
en el valor de qué definición, y por qué: `git diff` de la tabla lo dice constante a constante.

No importa la tabla ni `Meta/PurezaTitulares.lean`, para funcionar también cuando la tabla está desfasada y el build
falla en `#contrato_titulares`. No está en el build: es una herramienta.
-/

#contrato_generar "ROBINSON_PlusPlus/Meta/ContratoTabla.lean"

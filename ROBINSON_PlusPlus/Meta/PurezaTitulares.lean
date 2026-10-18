/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.PurezaComando
import ROBINSON_PlusPlus.Meta.Consistencia
import ROBINSON_PlusPlus.Meta.TarskiPrf
import ROBINSON_PlusPlus.Meta.Rosser
import ROBINSON_PlusPlus.Meta.Lob
import ROBINSON_PlusPlus.Meta.GodelCorolarios

/-!
# `Meta/PurezaTitulares.lean` — T08: el CONTROL DE PUREZA del cierre de los titulares de la clase (i) (ADR‑143)

**Por qué.** Desde ADR‑120 `ConsistentH` es un teorema (`consistencia`). Una hipótesis `hcon : ConsistentH` se descarga
sola, y el footprint no distingue «basta la consistencia» de «usa la verdad en ℕ»: si un lema de D1–D3 usara la
solidez de `Prf`, `hcon` quedaría de adorno con el MISMO footprint. Hasta hoy, lo único que lo impedía era la forma
del grafo de imports. Este módulo lo COMPRUEBA en cada `lake build`: si falla, el build no compila.

**Qué comprueba.** Para cada titular de la clase (i) de `TEOREMAS-E-HIPOTESIS.md` §1 (`PUROS`), su cierre de
dependencias no contiene ninguna constante de la SEMÁNTICA. El recorrido y el criterio están en
`Meta/PurezaComando.lean` (✏️ 2026‑10‑18, ADR‑157: separados de la lista, para que la lista pueda importar
`Meta/Rosser.lean`; los módulos de Rosser usan el comando `#pureza`, de allí).

**Controles positivos** (`IMPUROS`): `goedel_I`, `tarski` y `rosser` tienen que DISPARAR, porque llaman a
`consistencia`. Si no disparan, el criterio está ciego y el control falla igual. Visto fallar en los dos sentidos, con
un mutante (ADR‑143).

**Lo que NO comprueba**: el de `Meta/PurezaComando.lean`. Y no fija el ENUNCIADO de los titulares ni el valor de sus
definiciones: eso es T07, que irá en este mismo módulo.

Era el criterio de aceptación de Rosser (ADR‑137). ✏️ 2026‑10‑18 (ADR‑157): `rosser_ext` está en `PUROS`; y desde
ADR‑159, `lob`; y desde ADR‑162, los dos corolarios de la clase (i) de T78.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Lean Elab Command

namespace ROBINSON_PlusPlus.Meta.PurezaTitulares

/-- Los titulares de la clase (i): su prueba no usa el modelo. -/
def PUROS : List Name := [
  ``ROBINSON_PlusPlus.Meta.Representability2Prf.repr_pos'_prf,
  ``ROBINSON_PlusPlus.Meta.DerivCondPrf.d2_prf,
  ``ROBINSON_PlusPlus.Meta.PremsBdAllPrf.d3_prf_real,
  ``ROBINSON_PlusPlus.Meta.GodelTwoPrf.prf_godelCN_fixedpoint,
  ``ROBINSON_PlusPlus.Meta.GodelTwoPrf.prf_con_imp_godel,
  ``ROBINSON_PlusPlus.Meta.GodelTwoPrf.goedel_first_prf,
  ``ROBINSON_PlusPlus.Meta.GodelTwoPrf.goedel_second_prf,
  ``ROBINSON_PlusPlus.Meta.TarskiPrf.prf_tarski,
  ``ROBINSON_PlusPlus.Meta.Rosser.rosser_ext,
  ``ROBINSON_PlusPlus.Meta.Lob.lob,
  ``ROBINSON_PlusPlus.Meta.GodelCorolarios.prf_godel_iff_con,
  ``ROBINSON_PlusPlus.Meta.GodelCorolarios.goedel_second_formalizado]

/-- Los controles positivos: llaman a `consistencia`, así que su cierre TIENE que nombrar la semántica. -/
def IMPUROS : List Name := [
  ``ROBINSON_PlusPlus.Meta.Consistencia.goedel_I,
  ``ROBINSON_PlusPlus.Meta.TarskiPrf.tarski,
  ``ROBINSON_PlusPlus.Meta.Rosser.rosser]

/-- `#pureza_titulares`: el control, sobre `PUROS` e `IMPUROS`. -/
elab "#pureza_titulares" : command => ROBINSON_PlusPlus.Meta.PurezaComando.comprobar PUROS IMPUROS

end ROBINSON_PlusPlus.Meta.PurezaTitulares

#pureza_titulares

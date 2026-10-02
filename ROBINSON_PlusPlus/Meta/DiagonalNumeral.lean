/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.CodeNumeralPrf
import ROBINSON_PlusPlus.Meta.DiagonalTwo

/-!
> 🗑️ **2026‑10‑02 · ADR‑115 — leer antes que el resto.** La capa `⊢` se retiró de RPP, y con ella todo lo
> que este módulo tenía sobre `⊢`. Los nombres de esa capa que cite el texto de abajo
> (`hFN`, `diag_arith_num`, `provCode_transfer`, `godelCN_fixedpoint`, `goedel_first_numeral`,
> `goedel_first_undecidable_numeral`) **ya no existen**: lo que se lea sobre ellos es REGISTRO, no estado.
> Lo que queda en el módulo no depende de `⊢`.
-/

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.SubstArith
open ROBINSON_PlusPlus.Meta.Diagonal
open ROBINSON_PlusPlus.Meta.DiagonalTwo
open ROBINSON_PlusPlus.Meta.ProofChain
open ROBINSON_PlusPlus.Meta.CodeNumeralPrf
open FOL

set_option maxHeartbeats 1000000

namespace ROBINSON_PlusPlus.Meta.DiagonalNumeral

/-!
## META — **el lema diagonal con códigos NUMERALES** (la reparación de la inconsistencia)

🗑️ **2026‑10‑02 (ADR‑115):** este módulo reconstruía el punto fijo sobre `⊢` (`hFN`,
`diag_arith_num`, `provCode_transfer`, `godelCN_fixedpoint`) y Gödel I sobre él
(`goedel_first_numeral`, `goedel_first_undecidable_numeral`); todo se retiró con esa capa. **Hoy
sólo define la sentencia numeral** (`selfAppN`, `provCodeN`, `godelCN`). La reconstrucción vive
sobre `Prf` en `Meta/GodelTwoPrf.lean` §2: `prf_hFN`, `prf_diag_arith_num`, `prf_provCode_transfer`
y `prf_godelCN_fixedpoint`.

`Meta/Diagonal.lean` construía el punto fijo con `tc_form`, o sea con la lectura **sintáctica** de
`tcFn`, que era la que hacía inconsistente la teoría (`ax_tc_cons`, retirado de `axioms` en la
reparación). La reparación usa la lectura **NUMERAL**, que es consistente y tiene modelo en ℕ.

**La pieza que lo hace posible** es `prf_formCode_numeral` (`Meta/CodeNumeralPrf.lean`):
`formCode φ =eq numeral (codeNat φ)`. Con ella, `tcFn` sólo necesita `ax_tc_zero`/`ax_tc_succ`.

**Por qué la sustitución funciona sin refundar nada:** `prf_substFormula_arith (v) (s) (f)`
(`Meta/ArithPrf.lean`) acepta un `s` **ARBITRARIO**, luego traga un numeral igual que tragaba un
árbol; y `godelPred'`, `godelBeta'`, `diagTerm` y `godel_comp'` **no mencionan la representación
del código**, así que se reutilizan tal cual. El resultado se compone con `prf_provCode_transfer`
para dejarlo en la forma `godelCN ⇔ ¬ provCodeC' godelCN` que consume `goedel_first_prf` (⛔ vacuo
por `[AnclaEq]`, F1, ADR‑114).
-/

/-! ### La sentencia de Gödel, con el código escrito como NUMERAL -/

/-- `selfApp` con el código en forma numeral. -/
noncomputable def selfAppN (ψ : Formula) : Formula := substFormula 0 (numeral (codeNat ψ)) ψ

/-- `Prov'(⌜φ⌝)` con el código en forma numeral. -/
noncomputable def provCodeN (φ : Formula) : Formula :=
  substFormula 0 (numeral (codeNat φ)) provFormulaC'

/-- **Sentencia de Gödel numeral.** `godelBeta'` se reutiliza sin cambios. -/
noncomputable def godelCN : Formula := selfAppN godelBeta'

end ROBINSON_PlusPlus.Meta.DiagonalNumeral

export ROBINSON_PlusPlus.Meta.DiagonalNumeral (
  selfAppN
  provCodeN
  godelCN
)

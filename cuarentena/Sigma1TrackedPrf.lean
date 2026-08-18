/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.ExIntroCodePrf

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.ProofChain
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.TcArithPrf
open ROBINSON_PlusPlus.Meta.Representability2Prf
open ROBINSON_PlusPlus.Meta.DerivCondPrf
open ROBINSON_PlusPlus.Meta.Sigma1Prf
open ROBINSON_PlusPlus.Meta.Sigma1CorePrf
open ROBINSON_PlusPlus.Meta.ExIntroCodePrf

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace ROBINSON_PlusPlus.Meta.Sigma1TrackedPrf

/-!
## META — NIVEL D real (Opción A): verificación del ∃‑intro rastreado para testigos CONCRETOS

**Objetivo (RIESGO‑1, checkpoint del diseño `GODEL-D3-TRACKED-DESIGN.md` §7.1):** antes de
atacar el testigo **abstracto** de `hI_tracked`, verificar que la pieza L1 (∃‑intro a nivel
de código, `pcc_exIntro_code`) compone hasta `provCodeC'(∃A)` para un testigo **cerrado**
(concreto, p. ej. `objList lines`). Sube confianza en el álgebra De Bruijn/reconciliación
`exc ⌜A⌝ = ⌜∃A⌝` antes de la reformulación de raíz (Opción A, provFormulaC'ₜ/D1ₜ).

### Hallazgo (el muro del testigo abstracto)

El puente de la Opción A cierra para testigos **cerrados** (`pcc_exIntro_code_bridge` abajo):
`tcFn p` es cerrado sii `p` lo es, así que `hw` de `pcc_exIntro_code` se descarga. Para el
testigo **abstracto** (`p = #0` tras `prf_ex_elim_imp`), `tcFn #0` NO es cerrado y `hw` FALLA.
Análisis de sesión: todo combinador de reflexión base (`pcc_in_*`, `pcc_imp`, D1 `repr_pos'`)
produce códigos vía la `termCode` **meta**; transportarlos a la capa `tcFn` exige
`tcFn L =eq termCode L`, que está **meta‑stuck para `L` abstracta** (`termCode (runFn nil #0)`
no computa). `prf_tc_cons` sí computa `tcFn (cons a b)` abstractamente, pero no basta: el
cierre inductivo necesitaría que TODA la cadena `d3` viva en `tcFn` desde la raíz. Conclusión:
**`hI_tracked` abstracto requiere la Opción A de raíz** (redefinir `provFormulaC'ₜ`/`provCodeC'ₜ`
con `tcFn`/`substfc` + re‑derivar D1ₜ `repr_pos'_prfₜ`), no un lema incremental sobre lo actual.
Ver `GODEL-D3-TRACKED-DESIGN.md` §4.2 (DECISIÓN Opción A) para el plan A‑F1…A‑F5.
-/

/-- **Puente ∃‑intro rastreado → `provCodeC'` (testigo CERRADO)** — checkpoint RIESGO‑1.
    De la reflexión RASTREADA del código sustituido `provFromCode(substfc 0 (tcFn p) ⌜A⌝)`
    sale la reflexión real `provCodeC'(∃A)`, para `p` cerrado a todo nivel (concreto).
    Combina `pcc_exIntro_code` (∃‑intro a nivel de código, L1) con la reconciliación
    `exc ⌜A⌝ = ⌜∃A⌝` (definicional: `numeral 9 = succ⁹ zero`). El testigo `tcFn p` es cerrado
    porque `p` lo es (`hpc`), lo que descarga la hipótesis `hw` de `pcc_exIntro_code`. -/
theorem pcc_exIntro_code_bridge (A : Formula) (p : Term)
    (hpc : ∀ c, liftTerm c p = p)
    (h : Prf (provFromCode (substfc zero (tcFn p) (formCode A)))) :
    Prf (provCodeC' (Formula.ex A)) := by
  have hw : ∀ c, liftTerm c (tcFn p) = tcFn p := fun c => by
    simp only [tcFn, liftTerm, liftTerms, hpc c]
  have himp := pcc_exIntro_code (formCode A) (tcFn p) (fun c => liftTerm_formCode c A) hw
  -- himp : provFromCode (substfc zero (tcFn p) ⌜A⌝) ⇒ provFromCode (exc ⌜A⌝)
  -- exc ⌜A⌝ = ⌜∃A⌝, y provCodeC'(∃A) = provFromCode ⌜∃A⌝ (defeq: numeral 9 = succ⁹ zero)
  exact prf_mp himp h

/-- **Instancia concreta con `objList`**: para una cadena de prueba **explícita**
    `objList lines` cerrada (todos sus elementos cerrados), el ∃‑intro rastreado cierra.
    Confirma que el testigo concreto que produce `runFn`/`objList` (la forma soportada por
    `pcc_in_runFn_objList`) es admisible por la pieza L1. -/
theorem pcc_exIntro_code_objList (A : Formula) (lines : List Term)
    (hclosed : ∀ c, liftTerm c (objList lines) = objList lines)
    (h : Prf (provFromCode (substfc zero (tcFn (objList lines)) (formCode A)))) :
    Prf (provCodeC' (Formula.ex A)) :=
  pcc_exIntro_code_bridge A (objList lines) hclosed h

end ROBINSON_PlusPlus.Meta.Sigma1TrackedPrf

export ROBINSON_PlusPlus.Meta.Sigma1TrackedPrf (
  pcc_exIntro_code_bridge pcc_exIntro_code_objList
)

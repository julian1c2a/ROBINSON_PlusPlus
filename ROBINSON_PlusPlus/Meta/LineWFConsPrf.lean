/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.ChainOkBoundedPrf

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.ChainOkBoundedPrf

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Meta.LineWFConsPrf

/-!
## META — NIVEL D real (§36): buena‑formación estructural de las líneas del verificador

Para la reflexión punteada del átomo `In` (ruta B, `hI_dot`), la evaluación de `carc (nthc p i)`
—la conclusión de la línea `i`— requiere que `nthc p i` sea un **`cons`** (`carc` solo evalúa sobre
`cons`, `pcc_eval_carc`). Ese hecho lo provee `chainOk`: cada línea de una cadena válida está
**bien‑formada** (`lineWF`), y una línea bien‑formada es un `cons` (`ax_lineWF_cons`).

Cadena: `chainOk nil p` ⟹ (`chainOkB`, `prf_chainOk_iff_chainOkB`) `∀i<lenc p. lineOkB nil p i` ⟹
`lineWF (nthc p i)` ⟹ (`ax_lineWF_cons`) `nthc p i =eq cons (carc (nthc p i)) (cdrc (nthc p i))`.
-/

/-- **Una línea bien‑formada es un `cons`** (reflejo de `ax_lineWF_cons`):
    `⊢ lineWF line ⇒ line =eq cons (carc line) (cdrc line)`. -/
theorem prf_lineWF_cons (line : Term) :
    Prf (lineWF line ⇒ (line =eq cons (carc line) (cdrc line))) := by
  have hh := prf_spec (prf_ax (show ax_lineWF_cons ∈ axioms by simp [axioms])) line
  simpa [ax_lineWF_cons, substFormula, substTerm, substTerms, lineWF, carc, cdrc, cons,
    nil, zero, FOL.substTerm_liftTerm] using hh

/-- **`chainOk nil p` da `lineWF` de la línea `i`** (para `i < lenc p`). Vía `chainOkB` (que es
    `∀i<lenc p. lineOkB nil p i`) y `∧`‑elim izquierdo (`lineOkB = lineWF (nthc p i) ∧ …`). -/
theorem prf_chainOk_lineWF (p i : Term) :
    Prf (chainOk nil p ⇒ (lt i (lenc p) ⇒ lineWF (nthc p i))) := by
  refine prf_deduction (deduction_aux ?_ (lt i (lenc p)) [chainOk nil p] rfl)
  have hchain : PrfH [lt i (lenc p), chainOk nil p] (chainOk nil p) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hlt : PrfH [lt i (lenc p), chainOk nil p] (lt i (lenc p)) := PrfH.hyp _ _ (List.Mem.head _)
  have hB : PrfH [lt i (lenc p), chainOk nil p] (chainOkB nil p) :=
    PrfH_iff_mp (prf_chainOk_iff_chainOkB nil p) hchain
  have hspec := PrfH_spec hB i
  simp only [chainOkB, lineOkB, land, substFormula_boundedPremsIn, substFormula, substTerm,
    substTerms, lt, lenc, nthc, lineWF, premsOf, nil, zero, Nat.reduceEqDiff, reduceIte, if_true,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hspec
  exact PrfH_and_elim_left (PrfH.mp _ _ _ hspec hlt)

/-- **La línea `i`-ésima de una cadena válida es un `cons`**: `chainOk nil p ⇒ i < lenc p ⇒
    nthc p i =eq cons (carc (nthc p i)) (cdrc (nthc p i))`. Composición de `prf_chainOk_lineWF`
    con `prf_lineWF_cons`. Es la pieza que permite evaluar `carc (nthc p i)` en `hI_dot`. -/
theorem prf_line_is_cons (p i : Term) :
    Prf (chainOk nil p ⇒ (lt i (lenc p) ⇒
      (nthc p i =eq cons (carc (nthc p i)) (cdrc (nthc p i))))) := by
  refine prf_deduction (deduction_aux ?_ (lt i (lenc p)) [chainOk nil p] rfl)
  have hlw : PrfH [lt i (lenc p), chainOk nil p] (lineWF (nthc p i)) :=
    PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (prf_chainOk_lineWF p i) _)
      (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))) (PrfH.hyp _ _ (List.Mem.head _))
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_lineWF_cons (nthc p i)) _) hlw

end ROBINSON_PlusPlus.Meta.LineWFConsPrf

export ROBINSON_PlusPlus.Meta.LineWFConsPrf (
  prf_lineWF_cons prf_chainOk_lineWF prf_line_is_cons
)

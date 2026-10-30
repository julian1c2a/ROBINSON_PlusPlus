/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.ProofChain
import ROBINSON_PlusPlus.Meta.Representability
import ROBINSON_PlusPlus.Meta.CodeWitnessPrf

import FOL.FOL
import FOL.Theorems.Eq
import ROBINSON_PlusPlus.Meta.ReprPrf

/-!
> 🗑️ **2026‑10‑02 · ADR‑115 — leer antes que el resto.** La capa `⊢` se retiró de RPP, y con ella todo lo
> que este módulo tenía sobre `⊢`. Los nombres de esa capa que cite el texto de abajo
> (`repr_pos`, `vpf_run`) **ya no existen**: lo que se lea sobre ellos es REGISTRO, no estado.
> Lo que queda en el módulo no depende de `⊢`.
-/

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.SubstArith
open ROBINSON_PlusPlus.Meta.CheckArith
open ROBINSON_PlusPlus.Meta.HilbertSeq
open ROBINSON_PlusPlus.Meta.Representability
open ROBINSON_PlusPlus.Meta.ProofChain

namespace ROBINSON_PlusPlus.Meta.Representability2

/-!
## META — NIVEL D real: representabilidad positiva con `runFn` (R4-parte 2)

Re-construye `repr_pos` para el verificador estructural `runFn`/`chainOk` y el
predicado `provCodeC'`. Encoder **a medida** del nuevo formato: cada línea es
`cons ⌜concl⌝ (lineJustif …)` — la conclusión va incorporada como cabeza, de modo
que `carc` la extrae **uniformemente** (sin partir por reglas).

Este archivo arranca con el **runFn-tracking** (la mitad `In ⌜φ⌝`): `runFn` sobre
`proofCode' rs acc` calcula el código de la lista de conclusiones de `checkAux rs
acc`. Es RULE-AGNÓSTICO (solo usa `carc`), mucho más simple que el viejo `vpf_run`.
La validez `chainOk` (la otra mitad) sigue con los `lineWF`/`premsOf` por regla.

✏️ 2026‑10‑14 (ADR‑134): registro — el tracking y D1 ya no están aquí. ADR‑115 retiró sus versiones
sobre `⊢` (`runFn_track`, `In_runFn_of_mem`, `chainOk_track`, `repr_pos'`), y las vigentes, sobre
`Prf`, viven en `Meta/Representability2Prf.lean`: `prf_runFn_track`, `prf_In_runFn_of_mem`,
`prf_chainOk_track` y D1, `repr_pos'_prf`. Este módulo sólo conserva el encoder (`lineJustif`,
`lineCode'`, `proofCode'`) y las dos guardas de ADR‑020; las cuatro secciones vacías de abajo son
su rastro.
-/

/-! ### Encoder object del nuevo formato -/

/-- Justificación de una línea (etiqueta + parámetros), **sin** la conclusión
    (que va como cabeza en `lineCode'`). `mp`/`gen` transportan el código de la
    premisa resuelta; `thy` solo la etiqueta. -/
def lineJustif (acc : List Formula) : Rule → Term
  | .p1 A B => cons (numeralM 0) (cons (formCode A) (cons (formCode B) nil))
  | .p2 A B C => cons (numeralM 1) (cons (formCode A) (cons (formCode B) (cons (formCode C) nil)))
  | .c1 A B => cons (numeralM 2) (cons (formCode A) (cons (formCode B) nil))
  | .c2 A B => cons (numeralM 3) (cons (formCode A) (cons (formCode B) nil))
  | .c3 A B => cons (numeralM 4) (cons (formCode A) (cons (formCode B) nil))
  | .j1 A B => cons (numeralM 5) (cons (formCode A) (cons (formCode B) nil))
  | .j2 A B => cons (numeralM 6) (cons (formCode A) (cons (formCode B) nil))
  | .j3 A B C => cons (numeralM 7) (cons (formCode A) (cons (formCode B) (cons (formCode C) nil)))
  | .efq A => cons (numeralM 8) (cons (formCode A) nil)
  | .q1 A t => cons (numeralM 9) (cons (formCode A) (cons (termCode t) nil))
  | .q2 A t => cons (numeralM 10) (cons (formCode A) (cons (termCode t) nil))
  | .q3 A B => cons (numeralM 11) (cons (formCode A) (cons (formCode B) nil))
  | .eqrefl t => cons (numeralM 12) (cons (termCode t) nil)
  | .leibniz A t₁ t₂ =>
      cons (numeralM 13) (cons (formCode A) (cons (termCode t₁) (cons (termCode t₂) nil)))
  | .p3 A => cons (numeralM 14) (cons (formCode A) nil)
  | .ind A => cons (numeralM 18) (cons (formCode A) nil)
  | .qconf P C => cons (numeralM 19) (cons (formCode P) (cons (formCode C) nil))
  | .listInd A => cons (numeralM 20) (cons (formCode A) nil)
  | .thy _ => cons (numeralM 15) nil
  | .mp _ j => cons (numeralM 16) (cons (formCode ((acc[j]?).getD Formula.bottom)) nil)
  | .gen i => cons (numeralM 17) (cons (formCode ((acc[i]?).getD Formula.bottom)) nil)

/-- Línea completa: `cons ⌜concl⌝ justif`. La conclusión `f` (= `stepConcl acc r`)
    va como cabeza ⟹ `carc (lineCode' acc f r) =eq ⌜f⌝` para CUALQUIER regla. -/
def lineCode' (acc : List Formula) (f : Formula) (r : Rule) : Term :=
  cons (formCode f) (lineJustif acc r)

/-- Código object de una demostración-secuencia (nuevo formato). -/
def proofCode' : List Rule → List Formula → Term
  | [], _ => nil
  | r :: rs, acc =>
      match stepConcl acc r with
      | some f => cons (lineCode' acc f r) (proofCode' rs (acc ++ [f]))
      | none => nil

/-! ### runFn-tracking (mitad `In ⌜φ⌝`)

✏️ 2026‑10‑14 (ADR‑134): vacía desde ADR‑115; hoy `prf_runFn_track`, en `Meta/Representability2Prf.lean`. -/


/-! ### Pertenencia object de `φ` en las conclusiones

✏️ 2026‑10‑14 (ADR‑134): vacía desde ADR‑115; hoy `prf_In_runFn_of_mem`, en `Meta/Representability2Prf.lean`. -/


/-! ### chainOk-tracking (validez de la cadena)

✏️ 2026‑10‑14 (ADR‑134): vacía desde ADR‑115; hoy `prf_chainOk_track`, en `Meta/Representability2Prf.lean`. -/


/-! ### Pago de la guarda de los 7 esquemas enmendados (ADR-020)

Los esquemas `ax_lineWF_{q1,q2,q3,leibniz,ind,qconf,listInd}` piden `hasWitF`/`hasWit` de sus
ranuras. En una línea REAL esas ranuras son `formCode φ` / `termCode t`, y la **rama A** ya tenía
las dos piezas — sólo estaban inalcanzables: `CodeWitnessPrf` colgaba por debajo de este módulo
por **26 imports que no usaba**. Podados, sube, y la guarda se paga con dos líneas. -/

/-- `hasWitF` de un código de fórmula REAL. -/
theorem prf_hasWitF_fc (phi : Formula) : Prf (hasWitF (formCode phi)) :=
  formCodeM_eq phi ▸ prf_hasWitF_real phi

/-- `hasWit` de un código de término REAL. -/
theorem prf_hasWit_tc (t : Term) : Prf (hasWit (termCode t)) :=
  termCodeM_eq t ▸ CRIT_hasWit_real t


/-! ### Representabilidad positiva (D1) con el verificador estructural

✏️ 2026‑10‑14 (ADR‑134): vacía desde ADR‑115; hoy `repr_pos'_prf`, en `Meta/Representability2Prf.lean`. -/


end ROBINSON_PlusPlus.Meta.Representability2

export ROBINSON_PlusPlus.Meta.Representability2 (
  lineJustif
  lineCode'
  proofCode'
  -- ADR-020: los consumidores de aguas abajo PAGAN la guarda con estos dos.
  prf_hasWitF_fc prf_hasWit_tc
)

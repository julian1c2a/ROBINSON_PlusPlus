/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.Sigma1CorePrf
import ROBINSON_PlusPlus.Meta.Representability2Prf

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.Representability
open ROBINSON_PlusPlus.Meta.Sigma1Prf
open ROBINSON_PlusPlus.Meta.Sigma1CorePrf
open ROBINSON_PlusPlus.Meta.Representability2Prf

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Meta.InAxiomsCodePrf

/-!
## META — NIVEL D real (B.3c, caso `thy`): reflexión de `In (·) axiomsCodeT` en `Prov`

**Objetivo.** El caso `thy` (tag 15) de `pcc_lineWF_tracked` necesita producir
`Prov(⌜In (carc ṫ) axiomsCodeT⌝)` a partir de `In (carc t) axiomsCodeT` (que sale de `lineWF t`
vía el accesor `ax_lineWF_thy`). Es la **Σ₁‑completitud positiva de la pertenencia a axiomas** —
el groundwork de `NegVerifier` (`PLAN-NEGVERIFIER.md`).

### Por qué NO está bloqueado por Tarski (a diferencia del `In` abstracto genérico)

La reflexión genérica `In x L ⇒ provCodeC'(In x L)` para `x` **abstracto** SÍ está bloqueada: el
caso cabeza (`x =eq a`) exige reflejar la igualdad `x =eq a`, y `provCodeC'(x =eq a)` contiene
`termCode x` (meta, stuck para `x` abstracto) — obstrucción de Tarski.

**Pero el destino de `thy` NO usa `termCode (carc t)`, usa `carcT (tcFn t)`** (el `carc` a nivel de
código, RASTREADO), que `pcc_eval_carc` **evalúa** dentro de `Prov`. En el disyunto cabeza
`carc t =eq formCodeM f` (con `f` un axioma CONCRETO), la cadena
`carcT (tcFn t) →[pcc_eval_carc] tcFn (carc t) →[carc t = f̄] tcFn (formCodeM f) →[prf_tc_form]
termCode (formCodeM f)` deja el argumento en una forma **concreta**, y ahí la pertenencia es libre
(`repr_pos'_prf (prf_inAxiomsCodeT)`). El código rastreado **esquiva el muro**.

### Diseño de la recursión (pendiente — el grueso `NegVerifier`)

`pcc_In_lfc_tracked (yc y) (hbr : Prov(yc = tcFn y)) : ∀ L,
   Prf (In y (listFormCodeM L) ⇒ provFromCode (inFormCodeFn yc (termCode (listFormCodeM L))))`
por recursión sobre `L` (lista de axiomas ABSTRACTA — sin materializar el término gigante, como
`prf_In_listFormCodeM`):
* `L = []`: `In y nil` → explosión (`prf_not_in_nil`).
* `L = f :: fs`: `prf_in_cons_iff` da `y = formCodeM f ∨ In y (listFormCodeM fs)`; `PrfH_or_elim`:
  - cabeza (`y = formCodeM f`): **`pcc_in_head`** libre + swap del código `termCode (formCodeM f) → yc`
    por Leibniz DENTRO de `Prov` (`pcc_leibniz_code`), con la igualdad de códigos armada de
    `hbr` + `pcc_eq_tracked (y) (formCodeM f)` + `repr_pos'_prf (prf_tc_form f)`.
  - cola: **recursión** sobre `fs` + extensión de cola rastreada (reflejo de `ax_L2_in_cons` a
    códigos vía `pcc_thm_inst`).
Luego el **puente `axiomsCodeT ↔ listFormCodeM axioms`** ocurre DENTRO de `Prov` (Leibniz reflejada
del axioma `ax_axiomsCodeT_eq`), y la **evaluación de `carc t`** (`pcc_eval_carc` + `lineWF t` da la
estructura `cons`) conecta `carcT (tcFn t)` con el `yc` de la recursión.

### Lo que este módulo entrega ya (libre de muro)

El **payload del caso cabeza**: para un axioma CONCRETO, su pertenencia a `axiomsCodeT` es
demostrable DENTRO de `Prov` sin ningún muro — es `repr_pos'_prf` (D1) aplicado a la pertenencia
ya establecida `prf_inAxiomsCodeT`. Es la pieza que cada disyunto cabeza de la recursión consume.
-/

/-- **Pertenencia CONCRETA reflejada en `Prov`** (payload del caso cabeza de la recursión):
    para un axioma `f`, `Prov(⌜In ⌜f⌝ axiomsCodeT⌝)` es demostrable **libre de muro** — la
    pertenencia `In (formCode f) axiomsCodeT` es un `Prf` (`prf_inAxiomsCodeT` vía el meta‑axioma
    `prf_inAxC`) y D1 (`repr_pos'_prf`) la internaliza. -/
theorem pcc_inAxiomsCodeT_concrete {f : Formula} (hmem : f ∈ axioms) :
    Prf (provCodeC' (In (formCode f) axiomsCodeT)) := by
  have h0 : Prf (In (formCodeM f) axiomsCodeT) := prf_inAxC f hmem
  rw [formCodeM_eq] at h0
  exact repr_pos'_prf h0

end ROBINSON_PlusPlus.Meta.InAxiomsCodePrf

export ROBINSON_PlusPlus.Meta.InAxiomsCodePrf (
  pcc_inAxiomsCodeT_concrete
)

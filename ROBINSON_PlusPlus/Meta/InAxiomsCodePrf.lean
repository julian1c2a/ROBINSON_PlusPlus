/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.Sigma1CorePrf
import ROBINSON_PlusPlus.Meta.Representability2Prf
import ROBINSON_PlusPlus.Meta.MpCodePrf
import ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.Representability
open ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.TcArithPrf
open ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.Sigma1Prf
open ROBINSON_PlusPlus.Meta.Sigma1CorePrf
open ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
open ROBINSON_PlusPlus.Meta.MpCodePrf
open ROBINSON_PlusPlus.Meta.EvalNthcPrf
open ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf
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

/-! ### Distribución de `substfc` sobre el código‑`In` con hueco en el 1er argumento

Base de los *swaps* rastreados: sustituir el código‑testigo `t` en el hueco `⌜v₀⌝` de
`inFormCodeFn (⌜v₀⌝) Lc` lo mete en la primera posición (con `Lc` cerrado invariante). -/

/-- `substfc 0 t (inFormCodeFn ⌜v₀⌝ Lc) =eq inFormCodeFn t Lc` (con `Lc` `substtc`‑invariante). -/
theorem prf_substfc_inFormCode_hole1 (t Lc : Term)
    (hLinv : ∀ W, Prf (substtc zero W Lc =eq Lc)) :
    Prf (substfc zero t (inFormCodeFn (varc (numeral 0)) Lc) =eq inFormCodeFn t Lc) := by
  show Prf (substfc zero t (atomc (strCode in_sym) (cons (varc (numeral 0)) (cons Lc nil)))
    =eq atomc (strCode in_sym) (cons t (cons Lc nil)))
  refine prf_eq_trans
    (prf_substfc_atom zero t (strCode in_sym) (cons (varc (numeral 0)) (cons Lc nil))) ?_
  refine prf_congr_cons_tail (prf_congr_cons_tail (prf_congr_cons_head ?_))
  refine prf_eq_trans (prf_substtsc_cons zero t (varc (numeral 0)) (cons Lc nil)) ?_
  refine prf_eq_trans (prf_congr_cons_head (prf_substtc_varc0 t)) ?_
  refine prf_congr_cons_tail ?_
  exact prf_eq_trans (prf_substtsc_cons zero t Lc nil)
    (prf_eq_trans (prf_congr_cons_head (hLinv t)) (prf_congr_cons_tail (prf_substtsc_nil zero t)))

/-! ### `listFormCodeM L` es un CÓDIGO: `tcFn` lo computa (recursión sobre `L`) -/

/-- `tcFn (listFormCodeM L) =eq termCode (listFormCodeM L)` — el código de la lista de axiomas es
    un código genuino (`prf_tc_of_cons` + `prf_tc_form` en cada cabeza). -/
theorem prf_tc_listFormCodeM : ∀ L : List Formula,
    Prf (tcFn (listFormCodeM L) =eq termCode (listFormCodeM L))
  | [] => prf_tc_zero
  | f :: fs => by
      refine prf_tc_of_cons ?_ (prf_tc_listFormCodeM fs)
      rw [formCodeM_eq]; exact prf_tc_form f

/-- `termCode a` es `substtc`‑invariante cuando `a` está rastreado (copia local del de
    `LineWFTrackedPrf`, no importado aquí). -/
theorem substtc_inv_termCode_of_tc {a : Term} (htc : Prf (tcFn a =eq termCode a)) :
    ∀ W, Prf (substtc zero W (termCode a) =eq termCode a) := fun W =>
  prf_eq_trans (prf_congr_substtc3 (prf_eq_symm htc))
    (prf_eq_trans (prf_substtc_tcFn W a) htc)

/-- Corolario: `termCode (listFormCodeM L)` es `substtc`‑invariante. -/
theorem substtc_inv_termCode_listFormCodeM (L : List Formula) :
    ∀ W, Prf (substtc zero W (termCode (listFormCodeM L)) =eq termCode (listFormCodeM L)) :=
  substtc_inv_termCode_of_tc (prf_tc_listFormCodeM L)

/-! ### Combinador rastreado de COLA: extiende la lista‑código con `yc` fijo

Reflejo del teorema object `∀ x. In x t ⇒ In x (cons a t)` (vía `pcc_thm_inst` en el
código‑testigo `yc`), con el hueco `⌜v₀⌝` recibiendo `yc`. -/

/-- **Cola rastreada**: `Prov(⌜In yc t̃⌝) ⇒ Prov(⌜In yc (cons a t)~⌝)`, con `yc` código arbitrario. -/
theorem pcc_in_tail_tracked (yc a t : Term)
    (ht : ∀ W, Prf (substtc zero W (termCode t) =eq termCode t))
    (hat : ∀ W, Prf (substtc zero W (termCode (cons a t)) =eq termCode (cons a t))) :
    Prf (provFromCode (inFormCodeFn yc (termCode t)) ⇒
      provFromCode (inFormCodeFn yc (termCode (cons a t)))) := by
  have hgen : Prf (Formula.forall (Formula.impl (In (.var 0) t) (In (.var 0) (cons a t)))) :=
    Prf.gen _ (prf_in_cons_tail_imp a (.var 0) t)
  have hinst := pcc_thm_inst _ hgen yc
  have hcode : Prf (substfc zero yc (formCode (Formula.impl (In (.var 0) t) (In (.var 0) (cons a t))))
      =eq implc (inFormCodeFn yc (termCode t)) (inFormCodeFn yc (termCode (cons a t)))) := by
    refine prf_eq_trans (prf_substfc_impl zero yc (formCode (In (.var 0) t))
      (formCode (In (.var 0) (cons a t)))) ?_
    exact prf_congr_implc
      (prf_substfc_inFormCode_hole1 yc (termCode t) ht)
      (prf_substfc_inFormCode_hole1 yc (termCode (cons a t)) hat)
  exact prf_mp (pcc_mp_code_open _ _) (prf_mp (prf_provCode_congr hcode) hinst)

end ROBINSON_PlusPlus.Meta.InAxiomsCodePrf

export ROBINSON_PlusPlus.Meta.InAxiomsCodePrf (
  pcc_inAxiomsCodeT_concrete prf_substfc_inFormCode_hole1
  prf_tc_listFormCodeM substtc_inv_termCode_of_tc substtc_inv_termCode_listFormCodeM
  pcc_in_tail_tracked
)

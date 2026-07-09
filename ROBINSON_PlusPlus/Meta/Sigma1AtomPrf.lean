/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.TrackedCorePrf
import ROBINSON_PlusPlus.Meta.TcArithPrf

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.Sigma1Prf
open ROBINSON_PlusPlus.Meta.TcArithPrf
open ROBINSON_PlusPlus.Meta.DerivCondPrf
open ROBINSON_PlusPlus.Meta.TrackedCorePrf

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Meta.Sigma1AtomPrf

/-!
## META — NIVEL D real (§12‑A FASE 3, núcleo): toolkit RASTREADO del átomo `=eq`

Reflexión provable del átomo de igualdad `t =eq u`, para la Σ₁‑completitud provable del
verificador (`hbI`/`hbC` de `Meta/Sigma1BoundedPrf.lean`, cuyo átomo base es `nthc L i =eq x`).

**Por qué RASTREADO (y no libre de muro).** La reflexión de `t =eq u` para `t`, `u` **abstractos**
es imposible sin restricción (obstrucción de Tarski): `provCodeC'(t =eq u) = provFromCode(formCode(t
=eq u))` contiene `termCode t`/`termCode u` (**meta**, sin congruencia object), y `termCode t =eq
termCode u` NO se sigue de `t =eq u`. La salida estándar (Hilbert‑Bernays) es codificar los
argumentos con **`tcFn`** (que SÍ tiene congruencia Leibniz object, `prf_congr_tcFn`) y **discharge**
del puente `tcFn t =eq termCode t` cuando `t` es un numeral (`prf_tc_numeral`) — lo que hará la
inducción estructural de la fase 5.

Este módulo entrega el **átomo `=eq`** del toolkit rastreado, espejo exacto del de `In`
(`prf_provCodeC'_In_of_tracked`, `Meta/Sigma1CorePrf.lean`): constructor object `eqCodeFn`,
congruencia, clausura, transporte, y la reflexión rastreada `prf_provCodeC'_eq_of_tracked`.
-/

/-- Constructor object del código de `Formula.eq a b` desde los códigos `a`, `b` de sus términos:
    `⟨4, a, b⟩`. Espeja `formCode (.eq t u) = ⟨4, termCode t, termCode u⟩`. -/
def eqCodeFn (a b : Term) : Term :=
  cons (numeral 4) (cons a (cons b nil))

/-- **Puente definicional** con `formCode`: con los códigos meta `termCode`, `eqCodeFn` coincide
    con `formCode` de la igualdad (por definición de `formCode` sobre `.eq`). -/
theorem eqCodeFn_termCode (t u : Term) :
    eqCodeFn (termCode t) (termCode u) = formCode (Formula.eq t u) := rfl

/-- `provCodeC' (t =eq u)` es `provFromCode` del código con `termCode` (definicional). -/
theorem provCodeC'_eq_eq (t u : Term) :
    provCodeC' (Formula.eq t u) = provFromCode (eqCodeFn (termCode t) (termCode u)) := rfl

/-- **Clausura** de `eqCodeFn a b` bajo `liftTerm`: cerrado si `a`, `b` lo son. -/
theorem liftTerm_eqCodeFn (a b : Term)
    (ha : ∀ lvl, liftTerm lvl a = a) (hb : ∀ lvl, liftTerm lvl b = b) :
    ∀ lvl, liftTerm lvl (eqCodeFn a b) = eqCodeFn a b := by
  intro lvl
  simp only [eqCodeFn, cons, nil, zero, liftTerm, liftTerms, liftTerm_numeral, ha lvl, hb lvl]

/-- **Congruencia** de `eqCodeFn` en ambos argumentos (`Prf`). -/
theorem prf_congr_eqCodeFn {a a' b b' : Term}
    (ha : Prf (a =eq a')) (hb : Prf (b =eq b')) :
    Prf (eqCodeFn a b =eq eqCodeFn a' b') := by
  unfold eqCodeFn
  exact prf_congr_cons_tail
    (prf_eq_trans (prf_congr_cons_head ha) (prf_congr_cons_tail (prf_congr_cons_head hb)))

/-- **Transporte** de la demostrabilidad de una igualdad por igualdad de los códigos de sus
    términos (Leibniz object vía `provFromCode`). Espeja `prf_provFromCode_In_congr`. -/
theorem prf_provFromCode_eq_congr {a a' b b' : Term}
    (ha : Prf (a =eq a')) (hb : Prf (b =eq b')) :
    Prf (provFromCode (eqCodeFn a b) ⇒ provFromCode (eqCodeFn a' b')) :=
  prf_provCode_congr (prf_congr_eqCodeFn ha hb)

/-- **Clausura** de `provFromCode (eqCodeFn a b)` bajo `liftFormula` (args cerrados). -/
theorem liftFormula_provFromCode_eq (k : Nat) (a b : Term)
    (ha : ∀ lvl, liftTerm lvl a = a) (hb : ∀ lvl, liftTerm lvl b = b) :
    liftFormula k (provFromCode (eqCodeFn a b)) = provFromCode (eqCodeFn a b) :=
  liftFormula_provFromCode k (eqCodeFn a b) (liftTerm_eqCodeFn a b ha hb)

/-- **Reflexión RASTREADA del átomo `=eq`**: dada la demostrabilidad del código con argumentos
    rastreados `eqCodeFn tc uc` y los puentes `tc =eq termCode t`, `uc =eq termCode u`, se obtiene
    `provCodeC' (t =eq u)`. Espejo exacto de `prf_provCodeC'_In_of_tracked`.

    En la inducción (fase 5) los puentes se descargan cuando `t`, `u` son numerales
    (`tc = tcFn t`, `prf_tc_numeral`). -/
theorem prf_provCodeC'_eq_of_tracked {t u tc uc : Term}
    (ht : Prf (tc =eq termCode t)) (hu : Prf (uc =eq termCode u))
    (h : Prf (provFromCode (eqCodeFn tc uc))) :
    Prf (provCodeC' (Formula.eq t u)) :=
  prf_mp (prf_provFromCode_eq_congr ht hu) h

/-- **Reflexividad rastreada**: `provFromCode (eqCodeFn (tcFn t) (tcFn t))` — la igualdad
    reflexiva codificada con `tcFn` es demostrable. Se obtiene de la reflexión de `t =eq t`
    (teorema, `repr_pos'_prf (prf_refl t)`) transportada por `tcFn t =eq termCode t`... salvo el
    puente meta: se enuncia rastreado y el puente lo descarga la fase 5 (numerales). -/
theorem prf_provFromCode_eqCodeFn_refl_of_tracked {t tc : Term}
    (ht : Prf (tc =eq termCode t)) :
    Prf (provFromCode (eqCodeFn tc tc)) := by
  -- `provCodeC'(t =eq t) = provFromCode (eqCodeFn (termCode t) (termCode t))` (rfl), reflexividad
  have hrefl : Prf (provFromCode (eqCodeFn (termCode t) (termCode t))) :=
    repr_pos'_prf (prf_refl t)
  -- transporta `eqCodeFn (termCode t)(termCode t) ⇒ eqCodeFn tc tc` por `tc =eq termCode t` (simétrico)
  exact prf_mp (prf_provFromCode_eq_congr (prf_eq_symm ht) (prf_eq_symm ht)) hrefl

end ROBINSON_PlusPlus.Meta.Sigma1AtomPrf

export ROBINSON_PlusPlus.Meta.Sigma1AtomPrf (
  eqCodeFn eqCodeFn_termCode provCodeC'_eq_eq
  liftTerm_eqCodeFn prf_congr_eqCodeFn prf_provFromCode_eq_congr
  liftFormula_provFromCode_eq
  prf_provCodeC'_eq_of_tracked prf_provFromCode_eqCodeFn_refl_of_tracked
)

/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.Sigma1Prf
import ROBINSON_PlusPlus.Meta.TcArithPrf

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ProofChain
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.TcArithPrf
open ROBINSON_PlusPlus.Meta.Sigma1Prf

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace ROBINSON_PlusPlus.Meta.Sigma1CorePrf

/-!
## META — NIVEL D real: capa de **código object** para la reflexión de `In` (hacia `hI`)

Primer bloque de la reformulación al nivel del código object (Opción A). El
obstáculo de `hI : ∀x L, Prf (In x L ⇒ provCodeC'(In x L))` es que, para `L`
abstracta, `formCode (In x L)` contiene `termCode L` (**meta**, stuck): no hay
razonamiento object que iguale el código de un término abierto.

La salida es construir el código del átomo `In` con una **función object**
`inFormCodeFn` de los códigos `xc`, `Lc` de sus argumentos, de modo que la
demostrabilidad **respete la igualdad de esos códigos** (Leibniz object, vía
`provFromCode`). Combinada con `tcFn` (código del código, que sí computa sobre
términos-código concretos como el testigo) y `prf_congr_tcFn`, esto habilita el
transporte que la `formCode` meta bloqueaba.

Este módulo entrega el **constructor** `inFormCodeFn`, su **puente** definicional
con `formCode`, su **congruencia** en `Prf`, y el **transporte** de la
demostrabilidad por igualdad de los códigos de los argumentos. El cierre inductivo
final (construir el testigo con `tcFn`/`substfc`) —«la bestia»— se apoya sobre estas
piezas.
-/

/-! ### Constructor object del código de un átomo `In` -/

/-- Constructor object del **código de un átomo `In`** a partir de los códigos
    `xc`, `Lc` de sus dos argumentos: `⌜In · ·⌝ = ⟨3, ⌜∈⌝, [xc, Lc]⟩`.
    (Tag `3` = `atom`; `strCode in_sym` = símbolo `∈`.) -/
def inFormCodeFn (xc Lc : Term) : Term :=
  cons (numeral 3) (cons (strCode in_sym) (cons (cons xc (cons Lc nil)) nil))

/-- **Puente definicional**: el constructor con los códigos meta `termCode` de los
    argumentos coincide con `formCode` del átomo `In` (por definición de `formCode`
    sobre `.atom`). -/
theorem inFormCodeFn_termCode (x L : Term) :
    inFormCodeFn (termCode x) (termCode L) = formCode (In x L) := rfl

/-- `provCodeC'(In x L)` es `provFromCode` del código object del átomo (definicional). -/
theorem provCodeC'_In_eq (x L : Term) :
    provCodeC' (In x L) = provFromCode (inFormCodeFn (termCode x) (termCode L)) := rfl

/-! ### Congruencia y transporte -/

/-- **Congruencia** del constructor de código-`In` en ambos argumentos (`Prf`). -/
theorem prf_congr_inFormCodeFn {xc xc' Lc Lc' : Term}
    (hx : Prf (xc =eq xc')) (hL : Prf (Lc =eq Lc')) :
    Prf (inFormCodeFn xc Lc =eq inFormCodeFn xc' Lc') := by
  unfold inFormCodeFn
  exact prf_congr_cons_tail (prf_congr_cons_tail (prf_congr_cons_head
    (prf_eq_trans (prf_congr_cons_head hx) (prf_congr_cons_tail (prf_congr_cons_head hL)))))

/-- **Transporte de la demostrabilidad de un átomo `In` por igualdad de los códigos
    de sus argumentos** (Leibniz object vía `provFromCode`): de `xc =eq xc'` y
    `Lc =eq Lc'` sale
    `provFromCode (inFormCodeFn xc Lc) ⇒ provFromCode (inFormCodeFn xc' Lc')`.
    Es la pieza que parte la obstrucción de Tarski: en vez de la `formCode` meta,
    la demostrabilidad depende de los **códigos-término genuinos** `xc`, `Lc`. -/
theorem prf_provFromCode_In_congr {xc xc' Lc Lc' : Term}
    (hx : Prf (xc =eq xc')) (hL : Prf (Lc =eq Lc')) :
    Prf (provFromCode (inFormCodeFn xc Lc) ⇒ provFromCode (inFormCodeFn xc' Lc')) :=
  prf_provCode_congr (prf_congr_inFormCodeFn hx hL)

/-! ### Puente `tcFn` para el testigo: de la demostrabilidad **rastreada** a `provCodeC'`

En la inducción object sobre el testigo, el segundo argumento del átomo `In` es un
término object (p. ej. `runFn nil p`) cuyo código NO puede escribirse con la `termCode`
meta sin quedar stuck. La salida es rastrear su código con la **función object** `tcFn`
(código del código, que sí computa sobre términos-código concretos). El siguiente puente
conecta la demostrabilidad expresada con códigos rastreados `xc`/`Lc` con `provCodeC'(In x L)`
real, con tal de que esos códigos igualen (demostrablemente) a `termCode x`/`termCode L`.
Para argumentos que son **códigos** (numerales/`cons`/`nil`, como el testigo) esa igualdad
la dan los lemas `prf_tc_*` (`tcFn c =eq termCode c`). -/

/-- **Puente rastreado → `provCodeC'(In x L)`**: si la demostrabilidad del átomo `In`
    con los códigos rastreados `xc`, `Lc` es derivable, y `xc =eq termCode x`,
    `Lc =eq termCode L`, entonces `provCodeC'(In x L)` es derivable. -/
theorem prf_provCodeC'_In_of_tracked {x L xc Lc : Term}
    (hx : Prf (xc =eq termCode x)) (hL : Prf (Lc =eq termCode L))
    (h : Prf (provFromCode (inFormCodeFn xc Lc))) :
    Prf (provCodeC' (In x L)) :=
  prf_mp (prf_provFromCode_In_congr hx hL) h

/-- Especialización al uso real (`x = ⌜φ⌝` un código concreto, `L` un término-código):
    con `tcFn (formCode φ) =eq termCode (formCode φ)` (= `prf_tc_form`) para el 1er arg
    y `tcFn L =eq termCode L` para el 2º, la demostrabilidad rastreada da `provCodeC'`. -/
theorem prf_provCodeC'_In_formCode_of_tracked {φ : Formula} {L : Term}
    (hL : Prf (tcFn L =eq termCode L))
    (h : Prf (provFromCode (inFormCodeFn (tcFn (formCode φ)) (tcFn L)))) :
    Prf (provCodeC' (In (formCode φ) L)) :=
  prf_provCodeC'_In_of_tracked (prf_tc_form φ) hL h

end ROBINSON_PlusPlus.Meta.Sigma1CorePrf

export ROBINSON_PlusPlus.Meta.Sigma1CorePrf (
  inFormCodeFn inFormCodeFn_termCode provCodeC'_In_eq
  prf_congr_inFormCodeFn prf_provFromCode_In_congr
  prf_provCodeC'_In_of_tracked prf_provCodeC'_In_formCode_of_tracked
)

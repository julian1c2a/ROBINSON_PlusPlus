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
open ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ChainPrf
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

/-! ### Reflexión de `In` sobre listas explícitas (por meta-pertenencia)

Núcleo inductivo de `hI` para el caso en que la lista de conclusiones es una `cons`-lista
concreta (lo que produce `runFn` al evaluar el testigo). La reflexión de `In` sobre una lista
explícita se resuelve por **meta-inducción** en la lista, usando los combinadores object
`pcc_in_head`/`pcc_in_tail`/`pcc_in_nil`. Sortea la obstrucción de reflexión de igualdad:
en el caso cabeza el elemento **es** `x` (igualdad Lean, no `x =eq e` object), así que
`pcc_in_head` aplica **incondicionalmente**. -/

/-- Lista object (`cons`/`nil`) a partir de una lista meta de términos. -/
def objList : List Term → Term
  | []      => nil
  | e :: es => cons e (objList es)

/-- **Reflexión de `In` sobre una lista explícita** por meta-pertenencia: si `x` es
    (meta-)miembro de `elems`, entonces `provCodeC'(In x (objList elems))` es demostrable.
    Meta-inducción en `elems`; cabeza vía `pcc_in_head` (el elemento es `x`), cola vía
    `pcc_in_tail` + HI. (Se usa `List.Mem` explícito: `∈` está sobrecargado como el `In`
    object por la notación scoped de `Minimal.Axioms`.) -/
theorem pcc_in_objList_of_mem (x : Term) (elems : List Term) :
    List.Mem x elems → Prf (provCodeC' (In x (objList elems))) := by
  induction elems with
  | nil => intro h; cases h
  | cons e es ih =>
      intro h
      cases h with
      | head => exact pcc_in_head x (objList es)
      | tail _ hmem => exact prf_mp (pcc_in_tail e x (objList es)) (ih hmem)

/-! ### Tracking de `runFn` sobre cadenas explícitas → `objList` de conclusiones

`runFn c (cons line rest) = runFn (c ++ [carc line]) rest` acumula la **conclusión**
`carc line` de cada línea. Luego `runFn` sobre una cadena explícita `objList lines`
computa (=eq) el `objList` de las conclusiones `lines.map carc`. Con ello, la reflexión
de `In` sobre la lista de conclusiones (`pcc_in_objList_of_mem`) se transporta —vía
Leibniz object + `pcc_imp`— a la reflexión de `In x (runFn nil (objList lines))`. Es la
Σ₁-completitud de `In` para **testigos concretos** (cadenas de prueba explícitas). -/

/-- **Tracking `runFn` → `objList`** (acumulador general): `runFn c (objList lines)` computa
    `concat c (objList (lines.map carc))`. Meta-inducción en `lines` (usa `runFn_cons`,
    asociatividad de `concat` y `concat [h] X =eq cons h X`). -/
theorem prf_runFn_objList : ∀ (lines : List Term) (c : Term),
    Prf (runFn c (objList lines) =eq concat c (objList (lines.map carc)))
  | [], c => by exact prf_eq_trans (prf_runFn_nil c) (prf_eq_symm (prf_concat_nil_right c))
  | line :: rest, c => by
      have hstep := prf_runFn_cons c line (objList rest)
      have hih := prf_runFn_objList rest (concat c (cons (carc line) nil))
      have hassoc := prf_concat_assoc (cons (carc line) nil) (objList (rest.map carc)) c
      have hcons := prf_concat_cons_eq (carc line) nil (objList (rest.map carc))
      have hnil := prf_concat_nil_eq (objList (rest.map carc))
      have hconsFull := prf_eq_trans hcons (prf_congr_cons_tail hnil)
      have hcongr := prf_congr_concat_left (u := c) hconsFull
      exact prf_eq_trans hstep (prf_eq_trans hih (prf_eq_trans hassoc hcongr))

/-- **Tracking `runFn nil` → `objList`**: `runFn nil (objList lines) =eq objList (lines.map carc)`. -/
theorem prf_runFn_nil_objList (lines : List Term) :
    Prf (runFn nil (objList lines) =eq objList (lines.map carc)) :=
  prf_eq_trans (prf_runFn_objList lines nil) (prf_concat_nil_eq (objList (lines.map carc)))

/-- **Reflexión de `In` sobre `runFn` de una cadena explícita** (Σ₁-completitud de `In`
    para testigos concretos): si `x` es (meta-)miembro de las conclusiones `lines.map carc`,
    entonces `provCodeC'(In x (runFn nil (objList lines)))`. Reflexión sobre `objList`
    (`pcc_in_objList_of_mem`) + transporte por el tracking (`=eq` Leibniz object + `pcc_imp`). -/
theorem pcc_in_runFn_objList (x : Term) (lines : List Term)
    (hmem : List.Mem x (lines.map carc)) :
    Prf (provCodeC' (In x (runFn nil (objList lines)))) := by
  have hrefl := pcc_in_objList_of_mem x (lines.map carc) hmem
  have heq := prf_eq_symm (prf_runFn_nil_objList lines)
  have himp : Prf (In x (objList (lines.map carc)) ⇒ In x (runFn nil (objList lines))) :=
    prf_deduction (PrfH_eq_subst_in (prf_to_prfH heq _) (prfH_hyp_self _))
  exact prf_mp (pcc_imp himp) hrefl

/-! ### A‑F1 — `tcFn` computa `termCode` sobre las formas de lista de conclusiones

Hacia la capa rastreada uniforme (Opción A): `tcFn` (código del código, función object con
congruencia Leibniz) computa `termCode` sobre cualquier `objList` de **códigos** cuyos elementos
ya cumplan `tcFn = termCode`. En particular sobre `objList` de `formCode`s (la forma exacta de la
lista de conclusiones que produce `runFn`), cerrando el 2º argumento del puente rastreado
`prf_provCodeC'_In_formCode_of_tracked` (que exige `tcFn L =eq termCode L`). -/

/-- `tcFn = termCode` sobre `objList` de una lista de **códigos** que ya cumplen `tcFn = termCode`
    (meta-inducción; base `nil` vía `prf_tc_zero`, paso vía `prf_tc_of_cons`). -/
theorem prf_tc_objList (cs : List Term)
    (h : ∀ c, List.Mem c cs → Prf (tcFn c =eq termCode c)) :
    Prf (tcFn (objList cs) =eq termCode (objList cs)) := by
  induction cs with
  | nil => exact prf_tc_zero
  | cons c rest ih =>
      exact prf_tc_of_cons (h c (List.Mem.head _))
        (ih (fun d hd => h d (List.Mem.tail _ hd)))

/-- **`tcFn = termCode` sobre `objList` de `formCode`s** (la forma de la lista de conclusiones):
    especialización de `prf_tc_objList` con `prf_tc_form` en cada elemento. -/
theorem prf_tc_objList_formCode (φs : List Formula) :
    Prf (tcFn (objList (φs.map formCode)) =eq termCode (objList (φs.map formCode))) := by
  induction φs with
  | nil => exact prf_tc_zero
  | cons φ rest ih => exact prf_tc_of_cons (prf_tc_form φ) ih

/-! ### A‑F2 — puente: reflexión RASTREADA con testigo‑código = `provCodeC'` real

Mecanismo central de la Opción A. La reflexión de una fórmula sustituida se puede expresar con
**código object** `substfc (numeral 0) (tcFn p) (formCode A)` (sustitución object del código del
testigo `tcFn p` en el código `⌜A⌝`), y **coincide** con la `provCodeC'(A[0:=p])` real siempre que
el testigo `p` sea un **código** (`tcFn p =eq termCode p`). Prueba: `prf_substFormula_arith`
(el `substfc` object computa la `substFormula` meta sobre códigos) + congruencia `substfc`
(`prf_congr_substfc_arg2`) del testigo + transporte por igualdad de códigos (`prf_provCode_congr`).
El `tcFn` **NO se absorbe** (es slot‑término genuino), a diferencia de la `formCode` meta. -/

/-- **Puente rastreado→real de la Opción A**: si el testigo `p` es un código (`tcFn p =eq termCode p`)
    y la reflexión RASTREADA `provFromCode(substfc 0 (tcFn p) ⌜A⌝)` es derivable, entonces la
    reflexión real `provCodeC'(A[0:=p])` lo es. -/
theorem prf_provCodeC'_of_tracked_witness (A : Formula) (p : Term)
    (hp : Prf (tcFn p =eq termCode p))
    (h : Prf (provFromCode (substfc (numeral 0) (tcFn p) (formCode A)))) :
    Prf (provCodeC' (substFormula 0 p A)) := by
  have harith := prf_substFormula_arith 0 p A
  have hcongr := prf_congr_substfc_arg2 (x := numeral 0) (z := formCode A) hp
  have hchain := prf_eq_trans hcongr harith
  exact prf_mp (prf_provCode_congr hchain) h

end ROBINSON_PlusPlus.Meta.Sigma1CorePrf

export ROBINSON_PlusPlus.Meta.Sigma1CorePrf (
  inFormCodeFn inFormCodeFn_termCode provCodeC'_In_eq
  prf_congr_inFormCodeFn prf_provFromCode_In_congr
  prf_provCodeC'_In_of_tracked prf_provCodeC'_In_formCode_of_tracked
  objList pcc_in_objList_of_mem
  prf_runFn_objList prf_runFn_nil_objList pcc_in_runFn_objList
  prf_tc_objList prf_tc_objList_formCode
  prf_provCodeC'_of_tracked_witness
)

/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.Sigma1TrackedPrf

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.ProofChain
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.TcArithPrf
open ROBINSON_PlusPlus.Meta.Sigma1Prf
open ROBINSON_PlusPlus.Meta.Sigma1CorePrf
open ROBINSON_PlusPlus.Meta.DerivCondPrf

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace ROBINSON_PlusPlus.Meta.TrackedCorePrf

/-!
## META — NIVEL D real (Opción A DE RAÍZ): infraestructura de clausura genérica

Hacia **D1ₜ** (`repr_pos'_prfₜ`) y los combinadores rastreados. Primer ladrillo: la
**clausura de `provFromCode c` bajo `liftFormula`** para un **código cerrado arbitrario** `c`
(hoy solo existía para `provCodeC'` = `provFromCode ∘ formCode`, vía `liftFormula_provCodeC'`,
y para `exc Ac`, vía `liftFormula_provFromCode_exc`). La versión genérica la necesitan tanto
D1ₜ como el `∃`/MP a nivel de código con códigos `tcFn` (no `formCode`).

### Diagnóstico del cuello de botella (sesión 2026‑07‑05b)

`hI_tracked` abstracto necesita `provFromCode(inFormCodeFn (tcFn ⌜φ⌝) (tcFn L))` con `L`
abstracta. TODA vía por D1 (`repr_pos'`) emite el código vía `termCode` (meta); transportar el
2º argumento `termCode L → tcFn L` está **stuck** para `L` abstracta (el 1º, `⌜φ⌝` concreto, sí
transporta vía `prf_tc_form`). ⇒ **No hay atajo**: hay que **re‑derivar la representabilidad
emitiendo códigos `tcFn` nativamente** (reconstruir `proofCode'`/`runFn_track`/`chainOk_track`
de `Representability2Prf` en la capa `tcFn`). Eso es **D1ₜ**, el port grande. Este módulo abre
esa fase con la clausura genérica; ver `GODEL-D3-TRACKED-DESIGN.md` §4.2/§5 (Opción A).
-/

/-- **Clausura genérica de `provFromCode`**: para un código **cerrado** `c`
    (`∀ lvl, liftTerm lvl c = c`), `provFromCode c` es invariante bajo `liftFormula`.
    Generaliza `liftFormula_provCodeC'` (c = `formCode φ`) y `liftFormula_provFromCode_exc`
    (c = `exc Ac`). -/
theorem liftFormula_provFromCode (k : Nat) (c : Term) (hc : ∀ lvl, liftTerm lvl c = c) :
    liftFormula k (provFromCode c) = provFromCode c := by
  simp only [provFromCode, provFormulaC', substFormula, substTerm, substTerms, liftFormula,
    liftTerm, liftTerms, land, chainOk, In, runFn, nil, zero, Nat.reduceAdd, Nat.reduceLT,
    Nat.reduceEqDiff, Nat.reduceGT, Nat.reduceSub, reduceIte, Nat.zero_lt_succ, if_true,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift, hc]

/-- **Versión para códigos ABIERTOS**: sin exigir `c` cerrado, el `liftFormula` sobre
    `provFromCode c` se traslada al **código**: `liftFormula k (provFromCode c) = provFromCode (↑c)`.
    (El cuerpo Σ₁ `provFormulaC'` es cerrado; el único slot es `c`, que aparece bajo un binder — de
    ahí `liftTerm_comm_zero`.) Generaliza `liftFormula_provFromCode` (caso `c` cerrado).

    Es la pieza que necesita el **∀‑elim de código** (`prf_lineWF_q1` es estructural, igual que la
    línea Q2), donde el código abierto cae en el CONSECUENTE — al revés que en `pcc_exIntro_code'`. -/
theorem liftFormula_provFromCode_open (k : Nat) (c : Term) :
    liftFormula k (provFromCode c) = provFromCode (liftTerm k c) := by
  simp only [provFromCode, provFormulaC', substFormula, substTerm, substTerms, liftFormula,
    liftTerm, liftTerms, land, chainOk, In, runFn, nil, zero, Nat.reduceAdd, Nat.reduceLT,
    Nat.reduceEqDiff, Nat.reduceGT, Nat.reduceSub, reduceIte, Nat.zero_lt_succ, if_true,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift, ← FOL.liftTerm_comm_zero]

/-- **`substFormula` atraviesa `provFromCode`** y cae sobre el código:
    `substFormula v s (provFromCode c) = provFromCode (substTerm v s c)`.
    (El cuerpo Σ₁ es cerrado; el código está bajo un binder, de ahí `substTerm_lift_comm_zero`.)
    La necesita la **inducción object** sobre una fórmula de la forma `provFromCode (…#0…)`. -/
theorem substFormula_provFromCode_open (v : Nat) (s c : Term) :
    substFormula v s (provFromCode c) = provFromCode (substTerm v s c) := by
  have hz : (0 = v + 1) = False := eq_false (by omega)
  have hz2 : (0 > v + 1) = False := eq_false (by omega)
  simp only [provFromCode, provFormulaC', substFormula, substTerm, substTerms, liftTerm,
    liftTerms, land, chainOk, In, runFn, nil, zero, hz, hz2, if_false, Nat.reduceAdd,
    Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceGT, Nat.reduceSub, reduceIte, Nat.zero_lt_succ,
    if_true, FOL.substTerm_liftTerm, FOL.substTerm_liftLift, FOL.substTerm_lift_comm_zero]

/-!
### Constructores de código `tcFn`‑based para átomos binarios (§10.2, paso 1)

Todas las formas que el tracking refleja son **átomos binarios** `Formula.atom s [a, b]`
(`In`/`chainOk`/`allIn`), con el mismo esqueleto de código `⟨3, ⌜s⌝, [⌜a⌝, ⌜b⌝]⟩`. Generalizamos
el `inFormCodeFn` de `Sigma1CorePrf` (que era el caso `In`) a un **constructor object único**
`atom2CodeFn s a b`, con su puente definicional con `formCode`, su **congruencia** Leibniz y su
**clausura** (cerrado si los argumentos lo son). Son las piezas que D1ₜ emitirá para reflejar
`chainOk`/`In`/`allIn` con los argumentos rastreados por `tcFn` (en vez de `termCode` meta). -/

/-- Constructor object del código de un **átomo binario** `Formula.atom s [a, b]` a partir de los
    códigos `a`, `b` de sus argumentos: `⟨3, ⌜s⌝, [a, b]⟩`. Generaliza `inFormCodeFn` (s = `∈`). -/
def atom2CodeFn (s : String) (a b : Term) : Term :=
  cons (numeral 3) (cons (strCode s) (cons (cons a (cons b nil)) nil))

/-- **Puente definicional**: con los códigos meta `termCode` de los argumentos, `atom2CodeFn`
    coincide con `formCode` del átomo (por definición de `formCode` sobre `.atom`). -/
theorem atom2CodeFn_termCode (s : String) (a b : Term) :
    atom2CodeFn s (termCode a) (termCode b) = formCode (Formula.atom s [a, b]) := rfl

/-- `inFormCodeFn` es la instancia `s = in_sym` de `atom2CodeFn` (definicional). -/
theorem inFormCodeFn_eq_atom2 (xc Lc : Term) :
    inFormCodeFn xc Lc = atom2CodeFn in_sym xc Lc := rfl

/-- **Clausura** de `atom2CodeFn s a b` bajo `liftTerm`: cerrado si `a`, `b` lo son
    (el resto — `numeral 3`/`strCode s`/`cons`/`nil` — es cerrado). -/
theorem liftTerm_atom2CodeFn (s : String) (a b : Term)
    (ha : ∀ lvl, liftTerm lvl a = a) (hb : ∀ lvl, liftTerm lvl b = b) :
    ∀ lvl, liftTerm lvl (atom2CodeFn s a b) = atom2CodeFn s a b := by
  intro lvl
  simp only [atom2CodeFn, cons, nil, zero, liftTerm, liftTerms,
    liftTerm_numeral, liftTerm_strCode, ha lvl, hb lvl]

/-- **Congruencia** de `atom2CodeFn` en ambos argumentos (`Prf`). -/
theorem prf_congr_atom2CodeFn {s : String} {a a' b b' : Term}
    (ha : Prf (a =eq a')) (hb : Prf (b =eq b')) :
    Prf (atom2CodeFn s a b =eq atom2CodeFn s a' b') := by
  unfold atom2CodeFn
  exact prf_congr_cons_tail (prf_congr_cons_tail (prf_congr_cons_head
    (prf_eq_trans (prf_congr_cons_head ha) (prf_congr_cons_tail (prf_congr_cons_head hb)))))

/-- **Transporte** de la demostrabilidad de un átomo binario por igualdad de los códigos de sus
    argumentos (Leibniz object vía `provFromCode`). Generaliza `prf_provFromCode_In_congr`. -/
theorem prf_provFromCode_atom2_congr {s : String} {a a' b b' : Term}
    (ha : Prf (a =eq a')) (hb : Prf (b =eq b')) :
    Prf (provFromCode (atom2CodeFn s a b) ⇒ provFromCode (atom2CodeFn s a' b')) :=
  prf_provCode_congr (prf_congr_atom2CodeFn ha hb)

/-- **Clausura** de `provFromCode (atom2CodeFn s a b)` bajo `liftFormula` (args cerrados). -/
theorem liftFormula_provFromCode_atom2 (k : Nat) (s : String) (a b : Term)
    (ha : ∀ lvl, liftTerm lvl a = a) (hb : ∀ lvl, liftTerm lvl b = b) :
    liftFormula k (provFromCode (atom2CodeFn s a b)) = provFromCode (atom2CodeFn s a b) :=
  liftFormula_provFromCode k (atom2CodeFn s a b) (liftTerm_atom2CodeFn s a b ha hb)

/-! ### Instancias `chainOk` / `allIn` (los otros átomos del cuerpo Σ₁) -/

/-- Constructor object del código de `chainOk c p` desde los códigos `cc`, `pc`. -/
def chainOkCodeFn (cc pc : Term) : Term := atom2CodeFn "chainOk" cc pc

/-- Puente `chainOkCodeFn (termCode c) (termCode p) = formCode (chainOk c p)` (rfl). -/
theorem chainOkCodeFn_termCode (c p : Term) :
    chainOkCodeFn (termCode c) (termCode p) = formCode (chainOk c p) := rfl

/-- Constructor object del código de `allIn c L` desde los códigos `cc`, `Lc`. -/
def allInCodeFn (cc Lc : Term) : Term := atom2CodeFn "allIn" cc Lc

/-- Puente `allInCodeFn (termCode c) (termCode L) = formCode (allIn c L)` (rfl). -/
theorem allInCodeFn_termCode (c L : Term) :
    allInCodeFn (termCode c) (termCode L) = formCode (allIn c L) := rfl

end ROBINSON_PlusPlus.Meta.TrackedCorePrf

export ROBINSON_PlusPlus.Meta.TrackedCorePrf (
  liftFormula_provFromCode liftFormula_provFromCode_open substFormula_provFromCode_open
  atom2CodeFn atom2CodeFn_termCode inFormCodeFn_eq_atom2
  liftTerm_atom2CodeFn prf_congr_atom2CodeFn prf_provFromCode_atom2_congr
  liftFormula_provFromCode_atom2
  chainOkCodeFn chainOkCodeFn_termCode allInCodeFn allInCodeFn_termCode
)

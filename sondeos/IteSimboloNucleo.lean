/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.CodeDecode

/-!
# SONDEO · ¿qué rechaza el NÚCLEO al razonar a mano sobre `decodeTerm`?

**Fecha:** 2026‑10‑05 · **Encargo:** «mide para saber cuál de las dos notas es la cierta»: en
`Meta/CodeDecode.lean`, el docstring de `decodeTerm` («con `=` el núcleo rechaza el `split`; con `==` es
limpio») frente a la nota de la §B («el `if s == sym` sobre `DecidableEq String` es kernel‑frágil bajo
`split`/`rw`/`simp` manuales; se sortea con inducción funcional y `unfold`»). Nacieron en el mismo commit
(`9b178ae`, 2026‑07‑14) y se contradicen. Lean v4.31.0. Cada mensaje de error está FIJADO con `#guard_msgs`:
el sondeo compila, y deja de compilar si una versión de Lean cambia lo medido.

## Veredicto (MEDIDO: 59 teoremas; 24 mensajes fijados en 23 bloques `#guard_msgs`)

**Ninguna de las dos notas acierta en la causa.**

1. **El `if` sobre un símbolo NO es frágil** (§1, §2): 16 de 16 réplicas sin recursión —`String` o `List Char`
   × `==` o `=` × `split at h`, `rw [if_neg] at h`, `simp only [f, if_neg] at h`, `simp only [f]` + `split`—
   y 4 de 4 mutuas con llamadas a subtérminos DIRECTOS pasan el núcleo.
2. **Lo que el núcleo rechaza** (§3) es desplegar POR DEFEQ (`dsimp only [f] at h`, y `simp only [f] at h`)
   una recursión estructural MUTUA cuya llamada recursiva va a un subtérmino que sólo aparece tras un `match`
   interior sobre una VARIABLE. El elaborador lo acepta; el núcleo, no: `h` conserva su tipo original y el
   núcleo no lo reconoce igual al desplegado. 6 de 6 rechazadas: con `String` y con `List Char`, con `==`,
   con `=` y SIN comparar ningún símbolo (`mhNS_dsimp`, `mhNL_dsimp`: el `match` envuelto en `id`). El
   mensaje es el de julio: `Eq.mp (congrFun' (congrArg Eq (if_neg h✝)) (some _)) h`. Con `unfold f at h`
   (reescribe con `f.eq_def`, que es una PRUEBA) se aceptan las 12 variantes que lo usan (§3 y §4). Sin
   recursión mutua (`hondo*`, `h2*`), `dsimp` no despliega («`dsimp` made no progress») y no fabrica el
   término malo.
3. **En el decodificador real** (§4): `dsimp only [decodeTerm]` o `simp only [decodeTerm]`, y después
   `split at h` o `rw [if_neg] at h` → rechazadas (3 de 3); `unfold decodeTerm at h` y lo mismo → aceptadas
   (2 de 2); `decodeTerms` y `decodeChars` (llamadas a subtérminos DIRECTOS) con `dsimp` → aceptadas;
   `decodeForm` (no mutua): `dsimp`/`simp only` no lo despliegan, `unfold` sí y se acepta. Y con las formas
   CONCRETAS que da la inducción funcional (§4.2, el contexto de `decodeTerm_inj`), igual: `simp only
   [decodeTerm, hnat]` y `dsimp only [decodeTerm]` → rechazadas; `simp only [decodeForm, hnat]` → aceptada.
4. **Por qué** (§4.1; lo medido): `decodeTerm.eq_1` no es definicional —depende de `propext`, y `rfl` sobre la
   ecuación desplegada falla ya en el elaborador («Not a definitional equality»)—, pero `dsimp` despliega
   igual. INFERIDO (sin medir): el despliegue que usa `dsimp` para una recursión estructural mutua no
   coincide, bajo un `match` atascado, con lo que compila `TermG.brecOn` (`#print decodeTerm`); parece un
   defecto de Lean, y `mhNL_dsimp` es una reproducción mínima sin símbolos.

⇒ Con `decodeTerm` (mutua, llamada a `decodeTerms hts` bajo el `match` interior), `dsimp`/`simp only` sobre la
función, NUNCA: 5 de 5 formas rechazadas; `unfold`, sí. (`decodeTerms`, su pareja, llama a subtérminos directos y
`dsimp` pasa.) Con las no mutuas medidas —`decodeChars` con `dsimp`, `decodeForm` con `simp only` en forma
concreta— el núcleo acepta.

De la nota de la §B es cierto el SÍNTOMA (el cast `congrFun'` rechazado) y el REMEDIO (`unfold` en vez de
`dsimp`/`simp only`; la inducción funcional, que trae los casos ya reducidos); es falsa la CAUSA (ni el `if`,
ni `==`, ni `String`). Del docstring de `decodeTerm` es falso el diagnóstico entero: `=` y `==` dan lo mismo,
y la inyectividad no se prueba con `split`/`rw` sobre los `if`, sino con `decodeTerm.induct` y `unfold`.

Las réplicas `String` usan `TermG String` (el tipo de antes de D7) y `consS := "::"`; las `List Char`, el
`Term` y los `*_sym` de hoy.
-/

set_option autoImplicit false

open FOL
open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.CodeDecode

namespace IteSimboloNucleo

abbrev TS := TermG String
def consS : String := "::"
def zeroS : String := "0"

/-! ## 1 · Réplicas planas (sin recursión) -/

def bS : TS → Option Nat
  | .func cs [_, _] => if cs == consS then some 1 else none
  | _ => none
def pS : TS → Option Nat
  | .func cs [_, _] => if cs = consS then some 1 else none
  | _ => none
def bL : Term → Option Nat
  | .func cs [_, _] => if cs == cons_sym then some 1 else none
  | _ => none
def pL : Term → Option Nat
  | .func cs [_, _] => if cs = cons_sym then some 1 else none
  | _ => none

/-! ### 1.1 · `dsimp only [f] at h` y `split at h` sobre el `ite` -/

theorem bS_split (cs : String) (a b : TS) (n : Nat) (h : bS (.func cs [a, b]) = some n) :
    cs = consS := by
  dsimp only [bS] at h
  split at h
  · exact eq_of_beq ‹(cs == consS) = true›
  · simp at h

theorem pS_split (cs : String) (a b : TS) (n : Nat) (h : pS (.func cs [a, b]) = some n) :
    cs = consS := by
  dsimp only [pS] at h
  split at h
  · exact ‹cs = consS›
  · simp at h

theorem bL_split (cs : List Char) (a b : Term) (n : Nat) (h : bL (.func cs [a, b]) = some n) :
    cs = cons_sym := by
  dsimp only [bL] at h
  split at h
  · exact eq_of_beq ‹(cs == cons_sym) = true›
  · simp at h

theorem pL_split (cs : List Char) (a b : Term) (n : Nat) (h : pL (.func cs [a, b]) = some n) :
    cs = cons_sym := by
  dsimp only [pL] at h
  split at h
  · exact ‹cs = cons_sym›
  · simp at h

/-! ### 1.2 · `rw [if_neg] at h` -/

theorem bS_rw (cs : String) (a b : TS) (n : Nat) (h : bS (.func cs [a, b]) = some n) :
    cs = consS := by
  dsimp only [bS] at h
  by_cases hc : (cs == consS) = true
  · exact eq_of_beq hc
  · rw [if_neg hc] at h; simp at h

theorem pS_rw (cs : String) (a b : TS) (n : Nat) (h : pS (.func cs [a, b]) = some n) :
    cs = consS := by
  dsimp only [pS] at h
  by_cases hc : cs = consS
  · exact hc
  · rw [if_neg hc] at h; simp at h

theorem bL_rw (cs : List Char) (a b : Term) (n : Nat) (h : bL (.func cs [a, b]) = some n) :
    cs = cons_sym := by
  dsimp only [bL] at h
  by_cases hc : (cs == cons_sym) = true
  · exact eq_of_beq hc
  · rw [if_neg hc] at h; simp at h

theorem pL_rw (cs : List Char) (a b : Term) (n : Nat) (h : pL (.func cs [a, b]) = some n) :
    cs = cons_sym := by
  dsimp only [pL] at h
  by_cases hc : cs = cons_sym
  · exact hc
  · rw [if_neg hc] at h; simp at h

/-! ### 1.3 · `simp only [f, if_neg hc] at h` -/

theorem bS_simpneg (cs : String) (a b : TS) (n : Nat) (h : bS (.func cs [a, b]) = some n) :
    cs = consS := by
  by_cases hc : (cs == consS) = true
  · exact eq_of_beq hc
  · simp only [bS, if_neg hc] at h
    all_goals simp at h

theorem pS_simpneg (cs : String) (a b : TS) (n : Nat) (h : pS (.func cs [a, b]) = some n) :
    cs = consS := by
  by_cases hc : cs = consS
  · exact hc
  · simp only [pS, if_neg hc] at h
    all_goals simp at h

theorem bL_simpneg (cs : List Char) (a b : Term) (n : Nat) (h : bL (.func cs [a, b]) = some n) :
    cs = cons_sym := by
  by_cases hc : (cs == cons_sym) = true
  · exact eq_of_beq hc
  · simp only [bL, if_neg hc] at h
    all_goals simp at h

theorem pL_simpneg (cs : List Char) (a b : Term) (n : Nat) (h : pL (.func cs [a, b]) = some n) :
    cs = cons_sym := by
  by_cases hc : cs = cons_sym
  · exact hc
  · simp only [pL, if_neg hc] at h
    all_goals simp at h

/-! ### 1.4 · `simp only [f] at h` y `split at h` -/

theorem bS_simpsplit (cs : String) (a b : TS) (n : Nat) (h : bS (.func cs [a, b]) = some n) :
    cs = consS := by
  simp only [bS] at h
  split at h
  · exact eq_of_beq ‹(cs == consS) = true›
  · simp at h

theorem pS_simpsplit (cs : String) (a b : TS) (n : Nat) (h : pS (.func cs [a, b]) = some n) :
    cs = consS := by
  simp only [pS] at h
  split at h
  · exact ‹cs = consS›
  · simp at h

theorem bL_simpsplit (cs : List Char) (a b : Term) (n : Nat) (h : bL (.func cs [a, b]) = some n) :
    cs = cons_sym := by
  simp only [bL] at h
  split at h
  · exact eq_of_beq ‹(cs == cons_sym) = true›
  · simp at h

theorem pL_simpsplit (cs : List Char) (a b : Term) (n : Nat) (h : pL (.func cs [a, b]) = some n) :
    cs = cons_sym := by
  simp only [pL] at h
  split at h
  · exact ‹cs = cons_sym›
  · simp at h

/-! ## 2 · Réplicas MUTUAS con `match` y `&&`, llamadas recursivas a subtérminos DIRECTOS -/

mutual
def mbS : TS → Option Nat
  | .func cs [h, t] =>
      if cs == consS then
        match t with
        | .func c2 [_, .func c3 []] => if (c2 == consS) && (c3 == zeroS) then (mbsS h).map (· + 1) else none
        | _ => none
      else none
  | _ => none
def mbsS : TS → Option Nat
  | .func s [] => if s == zeroS then some 0 else none
  | .func s [h, t] => if s == consS then (mbS h).bind (fun x => (mbsS t).map (x + ·)) else none
  | _ => none
end

mutual
def mbL : Term → Option Nat
  | .func cs [h, t] =>
      if cs == cons_sym then
        match t with
        | .func c2 [_, .func c3 []] => if (c2 == cons_sym) && (c3 == zero_sym) then (mbsL h).map (· + 1) else none
        | _ => none
      else none
  | _ => none
def mbsL : Term → Option Nat
  | .func s [] => if s == zero_sym then some 0 else none
  | .func s [h, t] => if s == cons_sym then (mbL h).bind (fun x => (mbsL t).map (x + ·)) else none
  | _ => none
end

theorem mbS_split (cs : String) (h t : TS) (n : Nat) (hd : mbS (.func cs [h, t]) = some n) : cs = consS := by
  dsimp only [mbS] at hd
  split at hd
  · exact eq_of_beq ‹(cs == consS) = true›
  · simp at hd

theorem mbL_split (cs : List Char) (h t : Term) (n : Nat) (hd : mbL (.func cs [h, t]) = some n) :
    cs = cons_sym := by
  dsimp only [mbL] at hd
  split at hd
  · exact eq_of_beq ‹(cs == cons_sym) = true›
  · simp at hd

/-- El `&&` interior, partido a mano. -/
theorem mbS_split2 (cs c2 c3 : String) (h x : TS) (n : Nat)
    (hd : mbS (.func cs [h, .func c2 [x, .func c3 []]]) = some n) : And (c2 = consS) (c3 = zeroS) := by
  dsimp only [mbS] at hd
  split at hd
  · split at hd
    · rename_i hg
      simp only [Bool.and_eq_true, beq_iff_eq] at hg
      exact hg
    · simp at hd
  · simp at hd

theorem mbL_split2 (cs c2 c3 : List Char) (h x : Term) (n : Nat)
    (hd : mbL (.func cs [h, .func c2 [x, .func c3 []]]) = some n) : And (c2 = cons_sym) (c3 = zero_sym) := by
  dsimp only [mbL] at hd
  split at hd
  · split at hd
    · rename_i hg
      simp only [Bool.and_eq_true, beq_iff_eq] at hg
      exact hg
    · simp at hd
  · simp at hd

/-! ## 3 · El culpable, aislado

Recursión estructural cuya llamada recursiva va a un subtérmino que sólo aparece tras un `match` interior sobre
una VARIABLE, con ese `match` envuelto en algo que no es un `match`: un `if` (con `==` o con `=`, sobre `String` o
sobre `List Char`) o un simple `id`, sin comparar ningún símbolo. Frente a `llano`: llamada a un subtérmino
DIRECTO. -/

def hondoBS : TS → Option Nat
  | .func s [t] =>
      if s == consS then
        match t with
        | .func _ [u] => (hondoBS u).map (· + 1)
        | _ => some 0
      else none
  | _ => none
def hondoPS : TS → Option Nat
  | .func s [t] =>
      if s = consS then
        match t with
        | .func _ [u] => (hondoPS u).map (· + 1)
        | _ => some 0
      else none
  | _ => none
def hondoBL : Term → Option Nat
  | .func s [t] =>
      if s == cons_sym then
        match t with
        | .func _ [u] => (hondoBL u).map (· + 1)
        | _ => some 0
      else none
  | _ => none
def hondoPL : Term → Option Nat
  | .func s [t] =>
      if s = cons_sym then
        match t with
        | .func _ [u] => (hondoPL u).map (· + 1)
        | _ => some 0
      else none
  | _ => none
def hondoNS : TS → Option Nat
  | .func _ [t] =>
      id (
        match t with
        | .func _ [u] => (hondoNS u).map (· + 1)
        | _ => some 0
      )
  | _ => none
def hondoNL : Term → Option Nat
  | .func _ [t] =>
      id (
        match t with
        | .func _ [u] => (hondoNL u).map (· + 1)
        | _ => some 0
      )
  | _ => none
def llanoS : TS → Option Nat
  | .func _ [t] => (llanoS t).map (· + 1)
  | _ => some 0
def llanoL : Term → Option Nat
  | .func _ [t] => (llanoL t).map (· + 1)
  | _ => some 0

/--
error: `dsimp` made no progress
-/
#guard_msgs in
theorem hondoBS_dsimp (s : String) (t : TS) (n : Nat) (h : hondoBS (.func s [t]) = some n) :
    (if s == consS then match (generalizing := false) t with | .func _ [u] => (hondoBS u).map (· + 1) | _ => some 0 else none) = some n := by
  dsimp only [hondoBS] at h
  exact h
theorem hondoBS_unfold (s : String) (t : TS) (n : Nat) (h : hondoBS (.func s [t]) = some n) :
    (if s == consS then match (generalizing := false) t with | .func _ [u] => (hondoBS u).map (· + 1) | _ => some 0 else none) = some n := by
  unfold hondoBS at h
  exact h
/--
error: `dsimp` made no progress
-/
#guard_msgs in
theorem hondoPS_dsimp (s : String) (t : TS) (n : Nat) (h : hondoPS (.func s [t]) = some n) :
    (if s = consS then match (generalizing := false) t with | .func _ [u] => (hondoPS u).map (· + 1) | _ => some 0 else none) = some n := by
  dsimp only [hondoPS] at h
  exact h
theorem hondoPS_unfold (s : String) (t : TS) (n : Nat) (h : hondoPS (.func s [t]) = some n) :
    (if s = consS then match (generalizing := false) t with | .func _ [u] => (hondoPS u).map (· + 1) | _ => some 0 else none) = some n := by
  unfold hondoPS at h
  exact h
/--
error: `dsimp` made no progress
-/
#guard_msgs in
theorem hondoBL_dsimp (s : List Char) (t : Term) (n : Nat) (h : hondoBL (.func s [t]) = some n) :
    (if s == cons_sym then match (generalizing := false) t with | .func _ [u] => (hondoBL u).map (· + 1) | _ => some 0 else none) = some n := by
  dsimp only [hondoBL] at h
  exact h
theorem hondoBL_unfold (s : List Char) (t : Term) (n : Nat) (h : hondoBL (.func s [t]) = some n) :
    (if s == cons_sym then match (generalizing := false) t with | .func _ [u] => (hondoBL u).map (· + 1) | _ => some 0 else none) = some n := by
  unfold hondoBL at h
  exact h
/--
error: `dsimp` made no progress
-/
#guard_msgs in
theorem hondoPL_dsimp (s : List Char) (t : Term) (n : Nat) (h : hondoPL (.func s [t]) = some n) :
    (if s = cons_sym then match (generalizing := false) t with | .func _ [u] => (hondoPL u).map (· + 1) | _ => some 0 else none) = some n := by
  dsimp only [hondoPL] at h
  exact h
theorem hondoPL_unfold (s : List Char) (t : Term) (n : Nat) (h : hondoPL (.func s [t]) = some n) :
    (if s = cons_sym then match (generalizing := false) t with | .func _ [u] => (hondoPL u).map (· + 1) | _ => some 0 else none) = some n := by
  unfold hondoPL at h
  exact h
/--
error: `dsimp` made no progress
-/
#guard_msgs in
theorem hondoNS_dsimp (s : String) (t : TS) (n : Nat) (h : hondoNS (.func s [t]) = some n) :
    (id ( match (generalizing := false) t with | .func _ [u] => (hondoNS u).map (· + 1) | _ => some 0 )) = some n := by
  dsimp only [hondoNS] at h
  exact h
theorem hondoNS_unfold (s : String) (t : TS) (n : Nat) (h : hondoNS (.func s [t]) = some n) :
    (id ( match (generalizing := false) t with | .func _ [u] => (hondoNS u).map (· + 1) | _ => some 0 )) = some n := by
  unfold hondoNS at h
  exact h
/--
error: `dsimp` made no progress
-/
#guard_msgs in
theorem hondoNL_dsimp (s : List Char) (t : Term) (n : Nat) (h : hondoNL (.func s [t]) = some n) :
    (id ( match (generalizing := false) t with | .func _ [u] => (hondoNL u).map (· + 1) | _ => some 0 )) = some n := by
  dsimp only [hondoNL] at h
  exact h
theorem hondoNL_unfold (s : List Char) (t : Term) (n : Nat) (h : hondoNL (.func s [t]) = some n) :
    (id ( match (generalizing := false) t with | .func _ [u] => (hondoNL u).map (· + 1) | _ => some 0 )) = some n := by
  unfold hondoNL at h
  exact h

theorem llanoS_dsimp (s : String) (t : TS) (n : Nat) (h : llanoS (.func s [t]) = some n) :
    (llanoS t).map (· + 1) = some n := by
  dsimp only [llanoS] at h
  exact h

theorem llanoL_dsimp (s : List Char) (t : Term) (n : Nat) (h : llanoL (.func s [t]) = some n) :
    (llanoL t).map (· + 1) = some n := by
  dsimp only [llanoL] at h
  exact h

/-! ### 3.1 · Las dos formas de `decodeTerm` que faltaban: MUTUA, y con un discriminante que es una LLAMADA -/

mutual
def mhS : TS → Option Nat
  | .func cs [_, t] =>
      if cs == consS then
        match t with
        | .func _ [u] => (mhsS u).map (· + 1)
        | _ => none
      else none
  | _ => none
def mhsS : TS → Option Nat
  | .func s [h, t] => if s == consS then (mhS h).bind (fun x => (mhsS t).map (x + ·)) else none
  | _ => some 0
end
mutual
def mhL : Term → Option Nat
  | .func cs [_, t] =>
      if cs == cons_sym then
        match t with
        | .func _ [u] => (mhsL u).map (· + 1)
        | _ => none
      else none
  | _ => none
def mhsL : Term → Option Nat
  | .func s [h, t] => if s == cons_sym then (mhL h).bind (fun x => (mhsL t).map (x + ·)) else none
  | _ => some 0
end

mutual
def mhPS : TS → Option Nat
  | .func cs [_, t] =>
      if cs = consS then
        match t with
        | .func _ [u] => (mhsPS u).map (· + 1)
        | _ => none
      else none
  | _ => none
def mhsPS : TS → Option Nat
  | .func s [h, t] => if s = consS then (mhPS h).bind (fun x => (mhsPS t).map (x + ·)) else none
  | _ => some 0
end
mutual
def mhPL : Term → Option Nat
  | .func cs [_, t] =>
      if cs = cons_sym then
        match t with
        | .func _ [u] => (mhsPL u).map (· + 1)
        | _ => none
      else none
  | _ => none
def mhsPL : Term → Option Nat
  | .func s [h, t] => if s = cons_sym then (mhPL h).bind (fun x => (mhsPL t).map (x + ·)) else none
  | _ => some 0
end
mutual
def mhNS : TS → Option Nat
  | .func _ [_, t] =>
      id (
        match t with
        | .func _ [u] => (mhsNS u).map (· + 1)
        | _ => none
      )
  | _ => none
def mhsNS : TS → Option Nat
  | .func _ [h, t] => (mhNS h).bind (fun x => (mhsNS t).map (x + ·))
  | _ => some 0
end
mutual
def mhNL : Term → Option Nat
  | .func _ [_, t] =>
      id (
        match t with
        | .func _ [u] => (mhsNL u).map (· + 1)
        | _ => none
      )
  | _ => none
def mhsNL : Term → Option Nat
  | .func _ [h, t] => (mhNL h).bind (fun x => (mhsNL t).map (x + ·))
  | _ => some 0
end

def h2S : TS → Option Nat
  | .func s [h, t] =>
      if s == consS then
        match llanoS h, t with
        | some 0, .func _ [u] => (h2S u).map (· + 1)
        | _, _ => none
      else none
  | _ => none
def h2L : Term → Option Nat
  | .func s [h, t] =>
      if s == cons_sym then
        match llanoL h, t with
        | some 0, .func _ [u] => (h2L u).map (· + 1)
        | _, _ => none
      else none
  | _ => none

/--
error: (kernel) application type mismatch
  Eq.mp (congrFun' (congrArg Eq (if_neg h✝)) (some n)) h
argument has type
  mhS (TermG.func cs [a, t]) = some n
but function has type
  failed to pretty print expression (use 'set_option pp.rawOnError true' for raw representation)
-/
#guard_msgs in
theorem mhS_dsimp (cs : String) (a t : TS) (n : Nat) (h : mhS (.func cs [a, t]) = some n) : cs = consS := by
  dsimp only [mhS] at h
  split at h
  · exact eq_of_beq ‹(cs == consS) = true›
  · simp at h
/--
error: (kernel) application type mismatch
  Eq.mp (congrFun' (congrArg Eq (if_neg h✝)) (some n)) h
argument has type
  mhL (TermG.func cs [a, t]) = some n
but function has type
  failed to pretty print expression (use 'set_option pp.rawOnError true' for raw representation)
-/
#guard_msgs in
theorem mhL_dsimp (cs : List Char) (a t : Term) (n : Nat) (h : mhL (.func cs [a, t]) = some n) :
    cs = cons_sym := by
  dsimp only [mhL] at h
  split at h
  · exact eq_of_beq ‹(cs == cons_sym) = true›
  · simp at h
theorem mhL_unfold (cs : List Char) (a t : Term) (n : Nat) (h : mhL (.func cs [a, t]) = some n) :
    cs = cons_sym := by
  unfold mhL at h
  split at h
  · exact eq_of_beq ‹(cs == cons_sym) = true›
  · simp at h
/--
error: `dsimp` made no progress
-/
#guard_msgs in
theorem h2S_dsimp (cs : String) (a t : TS) (n : Nat) (h : h2S (.func cs [a, t]) = some n) : cs = consS := by
  dsimp only [h2S] at h
  split at h
  · exact eq_of_beq ‹(cs == consS) = true›
  · simp at h
/--
error: `dsimp` made no progress
-/
#guard_msgs in
theorem h2L_dsimp (cs : List Char) (a t : Term) (n : Nat) (h : h2L (.func cs [a, t]) = some n) :
    cs = cons_sym := by
  dsimp only [h2L] at h
  split at h
  · exact eq_of_beq ‹(cs == cons_sym) = true›
  · simp at h
theorem h2L_unfold (cs : List Char) (a t : Term) (n : Nat) (h : h2L (.func cs [a, t]) = some n) :
    cs = cons_sym := by
  unfold h2L at h
  split at h
  · exact eq_of_beq ‹(cs == cons_sym) = true›
  · simp at h


/--
error: (kernel) application type mismatch
  Eq.mp (congrFun' (congrArg Eq (if_neg h✝)) (some n)) h
argument has type
  mhPS (TermG.func cs [a, t]) = some n
but function has type
  failed to pretty print expression (use 'set_option pp.rawOnError true' for raw representation)
-/
#guard_msgs in
theorem mhPS_dsimp (cs : String) (a t : TS) (n : Nat) (h : mhPS (.func cs [a, t]) = some n) : cs = consS := by
  dsimp only [mhPS] at h
  split at h
  · exact ‹cs = consS›
  · simp at h
/--
error: (kernel) application type mismatch
  Eq.mp (congrFun' (congrArg Eq (if_neg h✝)) (some n)) h
argument has type
  mhPL (TermG.func cs [a, t]) = some n
but function has type
  failed to pretty print expression (use 'set_option pp.rawOnError true' for raw representation)
-/
#guard_msgs in
theorem mhPL_dsimp (cs : List Char) (a t : Term) (n : Nat) (h : mhPL (.func cs [a, t]) = some n) :
    cs = cons_sym := by
  dsimp only [mhPL] at h
  split at h
  · exact ‹cs = cons_sym›
  · simp at h
/--
error: (kernel) declaration type mismatch, 'IteSimboloNucleo.mhNS_dsimp' has type
  ∀ (cs : String) (a t : TS) (n : Nat), mhNS (TermG.func cs [a, t]) = some n → mhNS (TermG.func cs [a, t]) = some n
but it is expected to have type
  failed to pretty print expression (use 'set_option pp.rawOnError true' for raw representation)
-/
#guard_msgs in
/-- Sin `if` y sin comparar símbolos: el `match` interior, envuelto en `id`. -/
theorem mhNS_dsimp (cs : String) (a t : TS) (n : Nat) (h : mhNS (.func cs [a, t]) = some n) :
    id (match (generalizing := false) t with | .func _ [u] => (mhsNS u).map (· + 1) | _ => none) = some n := by
  dsimp only [mhNS] at h
  exact h
/--
error: (kernel) declaration type mismatch, 'IteSimboloNucleo.mhNL_dsimp' has type
  ∀ (cs : List Char) (a t : Term) (n : Nat), mhNL (TermG.func cs [a, t]) = some n → mhNL (TermG.func cs [a, t]) = some n
but it is expected to have type
  failed to pretty print expression (use 'set_option pp.rawOnError true' for raw representation)
-/
#guard_msgs in
theorem mhNL_dsimp (cs : List Char) (a t : Term) (n : Nat) (h : mhNL (.func cs [a, t]) = some n) :
    id (match (generalizing := false) t with | .func _ [u] => (mhsNL u).map (· + 1) | _ => none) = some n := by
  dsimp only [mhNL] at h
  exact h
theorem mhNL_unfold (cs : List Char) (a t : Term) (n : Nat) (h : mhNL (.func cs [a, t]) = some n) :
    id (match (generalizing := false) t with | .func _ [u] => (mhsNL u).map (· + 1) | _ => none) = some n := by
  unfold mhNL at h
  exact h

/-! ## 4 · El decodificador REAL de hoy (`List Char`, `==`), razonado a mano -/

/--
error: (kernel) application type mismatch
  Eq.mp (congrFun' (congrArg Eq (if_neg h✝)) (some x)) h
argument has type
  decodeTerm (TermG.func cs [hd, tl]) = some x
but function has type
  (if (cs == cons_sym) = true then
        match decodeNat hd, tl with
        | some 0, TermG.func c2 [hn, TermG.func c3 []] =>
          if (c2 == cons_sym && c3 == zero_sym) = true then Option.map TermG.var (decodeNat hn) else none
        | some 1, TermG.func c2 [hs, TermG.func c3 [hts, TermG.func c4 []]] =>
          if (c2 == cons_sym && c3 == cons_sym && c4 == zero_sym) = true then
            (decodeStr hs).bind fun s => Option.map (TermG.func s) (decodeTerms hts)
          else none
        | x, x_1 => none
      else none) =
      some x →
    none = some x
-/
#guard_msgs in
theorem real_dsimp_split (cs : List Char) (hd tl : Term) (x : Term)
    (h : decodeTerm (.func cs [hd, tl]) = some x) : cs = cons_sym := by
  dsimp only [decodeTerm] at h
  split at h
  · exact eq_of_beq ‹(cs == cons_sym) = true›
  · simp at h

/--
error: (kernel) application type mismatch
  Eq.mp (congrArg (fun _a => _a = some x) (if_neg hc)) h
argument has type
  decodeTerm (TermG.func cs [hd, tl]) = some x
but function has type
  (if (cs == cons_sym) = true then
        match decodeNat hd, tl with
        | some 0, TermG.func c2 [hn, TermG.func c3 []] =>
          if (c2 == cons_sym && c3 == zero_sym) = true then Option.map TermG.var (decodeNat hn) else none
        | some 1, TermG.func c2 [hs, TermG.func c3 [hts, TermG.func c4 []]] =>
          if (c2 == cons_sym && c3 == cons_sym && c4 == zero_sym) = true then
            (decodeStr hs).bind fun s => Option.map (TermG.func s) (decodeTerms hts)
          else none
        | x, x_1 => none
      else none) =
      some x →
    none = some x
-/
#guard_msgs in
theorem real_dsimp_rw (cs : List Char) (hd tl : Term) (x : Term)
    (h : decodeTerm (.func cs [hd, tl]) = some x) : cs = cons_sym := by
  dsimp only [decodeTerm] at h
  by_cases hc : (cs == cons_sym) = true
  · exact eq_of_beq hc
  · rw [if_neg hc] at h; simp at h

theorem real_unfold_split (cs : List Char) (hd tl : Term) (x : Term)
    (h : decodeTerm (.func cs [hd, tl]) = some x) : cs = cons_sym := by
  unfold decodeTerm at h
  split at h
  · exact eq_of_beq ‹(cs == cons_sym) = true›
  · simp at h

theorem real_unfold_rw (cs : List Char) (hd tl : Term) (x : Term)
    (h : decodeTerm (.func cs [hd, tl]) = some x) : cs = cons_sym := by
  unfold decodeTerm at h
  by_cases hc : (cs == cons_sym) = true
  · exact eq_of_beq hc
  · rw [if_neg hc] at h; simp at h

/--
error: (kernel) application type mismatch
  Eq.mp (congrFun' (congrArg Eq (if_neg h✝)) (some x)) h
argument has type
  decodeTerm (TermG.func cs [hd, tl]) = some x
but function has type
  (if (cs == cons_sym) = true then
        match decodeNat hd, tl with
        | some 0, TermG.func c2 [hn, TermG.func c3 []] =>
          if (c2 == cons_sym && c3 == zero_sym) = true then Option.map TermG.var (decodeNat hn) else none
        | some 1, TermG.func c2 [hs, TermG.func c3 [hts, TermG.func c4 []]] =>
          if (c2 == cons_sym && c3 == cons_sym && c4 == zero_sym) = true then
            (decodeStr hs).bind fun s => Option.map (TermG.func s) (decodeTerms hts)
          else none
        | x, x_1 => none
      else none) =
      some x →
    none = some x
-/
#guard_msgs in
theorem real_simp_split (cs : List Char) (hd tl : Term) (x : Term)
    (h : decodeTerm (.func cs [hd, tl]) = some x) : cs = cons_sym := by
  simp only [decodeTerm] at h
  split at h
  · exact eq_of_beq ‹(cs == cons_sym) = true›
  · simp at h

/-- `decodeTerms`, la otra mitad: sus llamadas van a subtérminos DIRECTOS. -/
theorem realTerms_dsimp_split (s : List Char) (a b : Term) (ts : List Term)
    (h : decodeTerms (.func s [a, b]) = some ts) : s = cons_sym := by
  dsimp only [decodeTerms] at h
  split at h
  · exact eq_of_beq ‹(s == cons_sym) = true›
  · simp at h

/-- `decodeChars` compara con `=` (Prop); su llamada va a un subtérmino DIRECTO. -/
theorem realChars_dsimp_split (s : List Char) (a b : Term) (cs : List Char)
    (h : decodeChars (.func s [a, b]) = some cs) : s = cons_sym := by
  dsimp only [decodeChars] at h
  split at h
  · exact ‹s = cons_sym›
  · simp at h

/--
error: `dsimp` made no progress
-/
#guard_msgs in
/-- `decodeForm` (no mutua; su llamada recursiva va a subtérminos HONDOS; compara con `=` arriba). -/
theorem realForm_dsimp_split (cs : List Char) (a b : Term) (φ : Formula)
    (h : decodeForm (.func cs [a, b]) = some φ) : cs = cons_sym := by
  dsimp only [decodeForm] at h
  split at h
  · exact ‹cs = cons_sym›
  · simp at h

/--
error: `simp` made no progress
-/
#guard_msgs in
theorem realForm_simp_split (cs : List Char) (a b : Term) (φ : Formula)
    (h : decodeForm (.func cs [a, b]) = some φ) : cs = cons_sym := by
  simp only [decodeForm] at h
  split at h
  · exact ‹cs = cons_sym›
  · simp at h

theorem realForm_unfold_split (cs : List Char) (a b : Term) (φ : Formula)
    (h : decodeForm (.func cs [a, b]) = some φ) : cs = cons_sym := by
  unfold decodeForm at h
  split at h
  · exact ‹cs = cons_sym›
  · simp at h

/-! ### 4.1 · Por qué (lo medible): la ecuación de `decodeTerm` NO es definicional -/

/--
info: 'ROBINSON_PlusPlus.Meta.CodeDecode.decodeTerm.eq_1' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms decodeTerm.eq_1

/--
error: Not a definitional equality: the left-hand side
  decodeTerm (TermG.func cs [hd, tl])
is not definitionally equal to the right-hand side
  if (cs == cons_sym) = true then
    match decodeNat hd, tl with
    | some 0, TermG.func c2 [hn, TermG.func c3 []] =>
      if (c2 == cons_sym && c3 == zero_sym) = true then Option.map TermG.var (decodeNat hn) else none
    | some 1, TermG.func c2 [hs, TermG.func c3 [hts, TermG.func c4 []]] =>
      if (c2 == cons_sym && c3 == cons_sym && c4 == zero_sym) = true then
        (decodeStr hs).bind fun s => Option.map (TermG.func s) (decodeTerms hts)
      else none
    | x, x_1 => none
  else none
---
error: (kernel) declaration type mismatch, 'IteSimboloNucleo.real_rfl' has type
  ∀ (cs : List Char) (hd tl : Term), decodeTerm (TermG.func cs [hd, tl]) = decodeTerm (TermG.func cs [hd, tl])
but it is expected to have type
  failed to pretty print expression (use 'set_option pp.rawOnError true' for raw representation)
-/
#guard_msgs in
theorem real_rfl (cs : List Char) (hd tl : Term) :
    decodeTerm (.func cs [hd, tl]) =
      (if (cs == cons_sym) = true then
        match decodeNat hd, tl with
        | some 0, .func c2 [hn, .func c3 []] =>
          if (c2 == cons_sym && c3 == zero_sym) = true then Option.map Term.var (decodeNat hn) else none
        | some 1, .func c2 [hs, .func c3 [hts, .func c4 []]] =>
          if (c2 == cons_sym && c3 == cons_sym && c4 == zero_sym) = true then
            (decodeStr hs).bind fun s => Option.map (Term.func s) (decodeTerms hts)
          else none
        | _, _ => none
      else none) := rfl

/-! ### 4.2 · Con las formas CONCRETAS que da la inducción funcional (el contexto de `decodeTerm_inj`) -/

/--
error: (kernel) application type mismatch
  congrArg Eq
    (ite_congr (Eq.refl ((cs == cons_sym) = true))
      (fun a =>
        Eq.trans
          (congrArg
            (fun x =>
              match x, TermG.func c2 [hn, TermG.func c3 []] with
              | some 0, TermG.func c2 [hn, TermG.func c3 []] =>
                if (c2 == cons_sym && c3 == zero_sym) = true then Option.map TermG.var (decodeNat hn) else none
              | some 1, TermG.func c2 [hs, TermG.func c3 [hts, TermG.func c4 []]] =>
                if (c2 == cons_sym && c3 == cons_sym && c4 == zero_sym) = true then
                  (decodeStr hs).bind fun s => Option.map (TermG.func s) (decodeTerms hts)
                else none
              | x, x_1 => none)
            hnat)
          (@decodeTerm.match_1.eq_1 (fun x t => Option Term) c2 hn c3
            (fun c2 hn c3 =>
              if (c2 == cons_sym && c3 == zero_sym) = true then Option.map TermG.var (decodeNat hn) else none)
            (fun c2 hs c3 hts c4 =>
              if (c2 == cons_sym && c3 == cons_sym && c4 == zero_sym) = true then
                (decodeStr hs).bind fun s => Option.map (TermG.func s) (decodeTerms hts)
              else none)
            fun x x_1 => none))
      fun a => Eq.refl none)
argument has type
  (if (cs == cons_sym) = true then
      match decodeNat hd, TermG.func c2 [hn, TermG.func c3 []] with
      | some 0, TermG.func c2 [hn, TermG.func c3 []] =>
        if (c2 == cons_sym && c3 == zero_sym) = true then Option.map TermG.var (decodeNat hn) else none
      | some 1, TermG.func c2 [hs, TermG.func c3 [hts, TermG.func c4 []]] =>
        if (c2 == cons_sym && c3 == cons_sym && c4 == zero_sym) = true then
          (decodeStr hs).bind fun s => Option.map (TermG.func s) (decodeTerms hts)
        else none
      | x, x_1 => none
    else none) =
    if (cs == cons_sym) = true then
      if (c2 == cons_sym && c3 == zero_sym) = true then Option.map TermG.var (decodeNat hn) else none
    else none
but function has type
  (decodeTerm (TermG.func cs [hd, TermG.func c2 [hn, TermG.func c3 []]]) =
      if (cs == cons_sym) = true then
        if (c2 == cons_sym && c3 == zero_sym) = true then Option.map TermG.var (decodeNat hn) else none
      else none) →
    Eq (decodeTerm (TermG.func cs [hd, TermG.func c2 [hn, TermG.func c3 []]])) =
      Eq
        (if (cs == cons_sym) = true then
          if (c2 == cons_sym && c3 == zero_sym) = true then Option.map TermG.var (decodeNat hn) else none
        else none)
-/
#guard_msgs in
theorem real_simp_concreto (cs c2 c3 : List Char) (hd hn : Term) (x : Term) (hnat : decodeNat hd = some 0)
    (h : decodeTerm (.func cs [hd, .func c2 [hn, .func c3 []]]) = some x) : cs = cons_sym := by
  simp only [decodeTerm, hnat] at h
  split at h
  · exact eq_of_beq ‹(cs == cons_sym) = true›
  · simp at h

/--
error: (kernel) application type mismatch
  Eq.mp
    (congrArg
      (fun _a =>
        (if (cs == cons_sym) = true then
            match _a, TermG.func c2 [hn, TermG.func c3 []] with
            | some 0, TermG.func c2 [hn, TermG.func c3 []] =>
              if (c2 == cons_sym && c3 == zero_sym) = true then Option.map TermG.var (decodeNat hn) else none
            | some 1, TermG.func c2 [hs, TermG.func c3 [hts, TermG.func c4 []]] =>
              if (c2 == cons_sym && c3 == cons_sym && c4 == zero_sym) = true then
                (decodeStr hs).bind fun s => Option.map (TermG.func s) (decodeTerms hts)
              else none
            | x, x_1 => none
          else none) =
          some x)
      hnat)
    h
argument has type
  decodeTerm (TermG.func cs [hd, TermG.func c2 [hn, TermG.func c3 []]]) = some x
but function has type
  (if (cs == cons_sym) = true then
        match decodeNat hd, TermG.func c2 [hn, TermG.func c3 []] with
        | some 0, TermG.func c2 [hn, TermG.func c3 []] =>
          if (c2 == cons_sym && c3 == zero_sym) = true then Option.map TermG.var (decodeNat hn) else none
        | some 1, TermG.func c2 [hs, TermG.func c3 [hts, TermG.func c4 []]] =>
          if (c2 == cons_sym && c3 == cons_sym && c4 == zero_sym) = true then
            (decodeStr hs).bind fun s => Option.map (TermG.func s) (decodeTerms hts)
          else none
        | x, x_1 => none
      else none) =
      some x →
    (if (cs == cons_sym) = true then
        match some 0, TermG.func c2 [hn, TermG.func c3 []] with
        | some 0, TermG.func c2 [hn, TermG.func c3 []] =>
          if (c2 == cons_sym && c3 == zero_sym) = true then Option.map TermG.var (decodeNat hn) else none
        | some 1, TermG.func c2 [hs, TermG.func c3 [hts, TermG.func c4 []]] =>
          if (c2 == cons_sym && c3 == cons_sym && c4 == zero_sym) = true then
            (decodeStr hs).bind fun s => Option.map (TermG.func s) (decodeTerms hts)
          else none
        | x, x_1 => none
      else none) =
      some x
-/
#guard_msgs in
theorem real_dsimp_concreto (cs c2 c3 : List Char) (hd hn : Term) (x : Term) (hnat : decodeNat hd = some 0)
    (h : decodeTerm (.func cs [hd, .func c2 [hn, .func c3 []]]) = some x) : cs = cons_sym := by
  dsimp only [decodeTerm] at h
  rw [hnat] at h
  split at h
  · exact eq_of_beq ‹(cs == cons_sym) = true›
  · simp at h

theorem realForm_simp_concreto (cs c3 : List Char) (h0 : Term) (φ : Formula) (hnat : decodeNat h0 = some 2)
    (h : decodeForm (.func cs [h0, .func c3 []]) = some φ) : cs = cons_sym := by
  simp only [decodeForm, hnat] at h
  split at h
  · exact ‹cs = cons_sym›
  · simp at h

end IteSimboloNucleo

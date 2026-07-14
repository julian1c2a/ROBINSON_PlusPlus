/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Minimal.Axioms

open ROBINSON_PlusPlus.Minimal.Axioms

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Meta.CodeDecode

/-!
## META — NIVEL D real (§43): DECODIFICADOR de códigos (módulo A de `PLAN-NEGVERIFIER.md`)

Inversos **computables** de los codificadores `numeralM` / `strCodeM` / `termCodeM` / `formCodeM`, con
sus **round‑trips** (`decodeX (codeX v) = some v`). Es la base de la **solidez estructural del
verificador** (`VerifierSound`, módulo E): de un testigo aceptado se recupera la lista de reglas real.

**Recursión estructural directa** sobre `Term` (`.func s args`) — así la terminación se infiere sola,
sin `termination_by` (los subtérminos aparecen en el patrón). Detalle De Bruijn: `nil = zero =
numeralM 0` (mismo término), de ahí el cuidado al distinguir «lista vacía» de «numeral 0».

**Nota (String es UTF‑8 en Lean v4.31.0):** `String` no es una estructura sobre `List Char`, así que el
round‑trip `String ↔ List Char` no es `rfl`; se cierra con **`String.ofList_toList`**.
-/

/-- Inverso de `numeralM`/`numeral`: `σⁿ0 ↦ n`. -/
def decodeNat : Term → Option Nat
  | .func s []  => if s = zero_sym then some 0 else none
  | .func s [t] => if s = succ_sym then (decodeNat t).map (· + 1) else none
  | _           => none

theorem decodeNat_numeralM (n : Nat) : decodeNat (numeralM n) = some n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [numeralM, succ, decodeNat, ih]; rfl

/-- Inverso de `charsCodeM` (lista de códigos de char). -/
def decodeChars : Term → Option (List Char)
  | .func s []     => if s = zero_sym then some [] else none
  | .func s [h, t] => if s = cons_sym then
                        (decodeNat h).bind (fun code =>
                          (decodeChars t).map (fun cs => Char.ofNat code :: cs))
                      else none
  | _ => none

/-- Inverso de `strCodeM`: código de símbolo `↦ String`. -/
def decodeStr (c : Term) : Option String := (decodeChars c).map String.ofList

theorem decodeChars_charsCodeM (cs : List Char) : decodeChars (charsCodeM cs) = some cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      simp only [charsCodeM, cons, decodeChars, decodeNat_numeralM, ih, Option.bind, Option.map,
        Char.ofNat_toNat, if_true]

theorem decodeStr_strCodeM (s : String) : decodeStr (strCodeM s) = some s := by
  simp only [decodeStr, strCodeM, decodeChars_charsCodeM, Option.map, String.ofList_toList]

/- Inverso de `termCodeM`/`termsCodeM` (mutuo). -/
mutual
/-- Inverso de `termCodeM` (los dos tags de término: `var`/`func`). -/
def decodeTerm : Term → Option Term
  | .func cs [h, t] =>
      if cs = cons_sym then
        match decodeNat h, t with
        | some 0, .func c2 [hn, .func c3 []] =>                          -- var n
            if (c2 == cons_sym) && (c3 == zero_sym) then (decodeNat hn).map Term.var else none
        | some 1, .func c2 [hs, .func c3 [hts, .func c4 []]] =>          -- func s ts
            if (c2 == cons_sym) && (c3 == cons_sym) && (c4 == zero_sym) then
              (decodeStr hs).bind (fun s => (decodeTerms hts).map (Term.func s))
            else none
        | _, _ => none
      else none
  | _ => none
def decodeTerms : Term → Option (List Term)
  | .func s []     => if s = zero_sym then some [] else none
  | .func s [h, t] => if s = cons_sym then
                        (decodeTerm h).bind (fun x => (decodeTerms t).map (x :: ·))
                      else none
  | _ => none
end

mutual
theorem decodeTerm_termCodeM (t : Term) : decodeTerm (termCodeM t) = some t := by
  cases t with
  | var n => simp [termCodeM, cons, nil, zero, decodeTerm, decodeNat_numeralM]
  | func s ts => simp [termCodeM, cons, nil, zero, decodeTerm, decodeNat_numeralM,
      decodeStr_strCodeM, decodeTerms_termsCodeM ts]
theorem decodeTerms_termsCodeM (ts : List Term) : decodeTerms (termsCodeM ts) = some ts := by
  cases ts with
  | nil => rfl
  | cons t ts => simp [termsCodeM, cons, decodeTerms, decodeTerm_termCodeM t,
      decodeTerms_termsCodeM ts]
end

/-- Inverso de `formCodeM` (los 9 tags de fórmula). Recursión estructural sobre las subfórmulas. -/
def decodeForm : Term → Option Formula
  | .func cs [h, t] =>
      if cs = cons_sym then
        match decodeNat h, t with
        | some 2, .func c3 [] =>                                         -- ⊥
            if c3 == zero_sym then some .bottom else none
        | some 3, .func c2 [hp, .func c3 [hts, .func c4 []]] =>          -- atom p ts
            if (c2 == cons_sym) && (c3 == cons_sym) && (c4 == zero_sym) then
              (decodeStr hp).bind (fun p => (decodeTerms hts).map (Formula.atom p))
            else none
        | some 4, .func c2 [ha, .func c3 [hb, .func c4 []]] =>           -- t = u
            if (c2 == cons_sym) && (c3 == cons_sym) && (c4 == zero_sym) then
              (decodeTerm ha).bind (fun a => (decodeTerm hb).map (Formula.eq a))
            else none
        | some 5, .func c2 [ha, .func c3 [hb, .func c4 []]] =>           -- a ⇒ b
            if (c2 == cons_sym) && (c3 == cons_sym) && (c4 == zero_sym) then
              match decodeForm ha, decodeForm hb with
              | some a, some b => some (Formula.impl a b) | _, _ => none
            else none
        | some 6, .func c2 [ha, .func c3 []] =>                          -- ∀ a
            if (c2 == cons_sym) && (c3 == zero_sym) then (decodeForm ha).map Formula.forall else none
        | some 7, .func c2 [ha, .func c3 [hb, .func c4 []]] =>           -- a ∧ b
            if (c2 == cons_sym) && (c3 == cons_sym) && (c4 == zero_sym) then
              match decodeForm ha, decodeForm hb with
              | some a, some b => some (Formula.and a b) | _, _ => none
            else none
        | some 8, .func c2 [ha, .func c3 [hb, .func c4 []]] =>           -- a ∨ b
            if (c2 == cons_sym) && (c3 == cons_sym) && (c4 == zero_sym) then
              match decodeForm ha, decodeForm hb with
              | some a, some b => some (Formula.or a b) | _, _ => none
            else none
        | some 9, .func c2 [ha, .func c3 []] =>                          -- ∃ a
            if (c2 == cons_sym) && (c3 == zero_sym) then (decodeForm ha).map Formula.ex else none
        | _, _ => none
      else none
  | _ => none

theorem decodeForm_formCodeM (φ : Formula) : decodeForm (formCodeM φ) = some φ := by
  induction φ with
  | bottom => rfl
  | atom p ts => simp [formCodeM, cons, nil, zero, decodeForm, decodeNat_numeralM,
      decodeStr_strCodeM, decodeTerms_termsCodeM]
  | eq t u => simp [formCodeM, cons, nil, zero, decodeForm, decodeNat_numeralM, decodeTerm_termCodeM]
  | impl a b iha ihb => simp [formCodeM, cons, nil, zero, decodeForm, decodeNat_numeralM, iha, ihb]
  | «forall» a ih => simp [formCodeM, cons, nil, zero, decodeForm, decodeNat_numeralM, ih]
  | and a b iha ihb => simp [formCodeM, cons, nil, zero, decodeForm, decodeNat_numeralM, iha, ihb]
  | or a b iha ihb => simp [formCodeM, cons, nil, zero, decodeForm, decodeNat_numeralM, iha, ihb]
  | ex a ih => simp [formCodeM, cons, nil, zero, decodeForm, decodeNat_numeralM, ih]

end ROBINSON_PlusPlus.Meta.CodeDecode

export ROBINSON_PlusPlus.Meta.CodeDecode (
  decodeNat decodeNat_numeralM
  decodeChars decodeStr decodeChars_charsCodeM decodeStr_strCodeM
  decodeTerm decodeTerms decodeTerm_termCodeM decodeTerms_termsCodeM
  decodeForm decodeForm_formCodeM
)

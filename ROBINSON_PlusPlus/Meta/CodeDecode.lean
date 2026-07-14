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

/-- Inverso de `charsCodeM` (lista de códigos de char). El guard `(Char.ofNat code).toNat == code`
    rechaza códigos que `Char.ofNat` **clamparía** (fuera del rango Unicode) — así el decodificador es
    genuinamente **inyectivo** (necesario para `decodeChars_inj`). El round‑trip lo cumple porque
    `Char.ofNat c.toNat = c`, luego `(Char.ofNat c.toNat).toNat = c.toNat`. -/
def decodeChars : Term → Option (List Char)
  | .func s []     => if s = zero_sym then some [] else none
  | .func s [h, t] => if s = cons_sym then
                        (decodeNat h).bind (fun code =>
                          if (Char.ofNat code).toNat == code then
                            (decodeChars t).map (fun cs => Char.ofNat code :: cs)
                          else none)
                      else none
  | _ => none

/-- Inverso de `strCodeM`: código de símbolo `↦ String`. -/
def decodeStr (c : Term) : Option String := (decodeChars c).map String.ofList

theorem decodeChars_charsCodeM (cs : List Char) : decodeChars (charsCodeM cs) = some cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      simp only [charsCodeM, cons, decodeChars, decodeNat_numeralM, ih, Option.bind, Option.map,
        Char.ofNat_toNat, beq_self_eq_true, if_true]

theorem decodeStr_strCodeM (s : String) : decodeStr (strCodeM s) = some s := by
  simp only [decodeStr, strCodeM, decodeChars_charsCodeM, Option.map, String.ofList_toList]

/- Inverso de `termCodeM`/`termsCodeM` (mutuo). -/
mutual
/-- Inverso de `termCodeM` (los dos tags de término: `var`/`func`).

    ⚠️ Las comparaciones de símbolo van con **`==` (Bool)**, NO con `= … then` (Prop). Es
    deliberado: `decodeTerm`/`decodeTerms` son **mutuas** ⇒ sin `fun_induction`, y la inyectividad se
    prueba con `split`/`rw` sobre los `if`. Un `if (s = sym)` sobre `DecidableEq String` hace que
    `split`/`if_pos` fabriquen un cast de instancia que el **núcleo rechaza**; con `==` los `split` son
    limpios. (`decodeNat`/`decodeChars`/`decodeForm` no lo necesitan: usan `fun_induction`.) -/
def decodeTerm : Term → Option Term
  | .func cs [h, t] =>
      if cs == cons_sym then
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
  | .func s []     => if s == zero_sym then some [] else none
  | .func s [h, t] => if s == cons_sym then
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

/-!
## La dirección CRÍTICA (§43·B): INYECTIVIDAD del decodificador

`decodeX c = some v → c = codeX v`: si un término **decodifica**, es **exactamente** el código de lo
decodificado. Es la pieza que hace el trabajo en `VerifierSound` (módulo E): de un testigo aceptado por
el verificador se recupera —de forma **única**— la derivación real.

**Nota de implementación (kernel + De Bruijn).** El `if s == sym` sobre `DecidableEq String` es
kernel‑frágil bajo `split`/`rw`/`simp` manuales (fabrican un cast `congrFun'` que el núcleo rechaza).
Se evita usando **inducción funcional** (`fun_induction` / `.induct`), que genera los casos ya reducidos
—como en los round‑trips— y `unfold … at h` (limpio) donde hace falta destapar la definición.
-/

/-- Inyectividad de `decodeNat` (⟸ del round‑trip). -/
theorem decodeNat_inj {t : Term} {n : Nat} (h : decodeNat t = some n) : t = numeralM n := by
  fun_induction decodeNat t generalizing n
  · injection h with h; subst h; rfl
  · simp at h
  · rename_i t' ih
    rcases hm : decodeNat t' with _ | m
    · rw [hm] at h; simp at h
    · rw [hm] at h; simp only [Option.map] at h; injection h with h; subst h
      have := ih hm; subst this; rfl
  · simp at h
  · simp at h

/-- Inyectividad de `decodeChars` (el guard de validez de char es lo que la hace cierta). -/
theorem decodeChars_inj {c : Term} {cs : List Char} (h : decodeChars c = some cs) :
    c = charsCodeM cs := by
  fun_induction decodeChars c generalizing cs
  · injection h with h; subst h; rfl
  · simp at h
  · rename_i hd t' ih
    rcases hnat : decodeNat hd with _ | code
    · rw [hnat] at h; simp at h
    · rw [hnat] at h; simp only [Option.bind] at h
      split at h
      · rename_i hguard
        rcases hrec : decodeChars t' with _ | cs'
        · rw [hrec] at h; simp at h
        · rw [hrec] at h; simp only [Option.map] at h; injection h with h; subst h
          have e1 := decodeNat_inj hnat
          have e2 := ih hrec
          subst e1 e2
          rw [beq_iff_eq] at hguard
          simp only [charsCodeM, cons]; rw [hguard]
      · simp at h
  · simp at h
  · simp at h

/-- Inyectividad de `decodeStr`. -/
theorem decodeStr_inj {c : Term} {s : String} (h : decodeStr c = some s) : c = strCodeM s := by
  simp only [decodeStr] at h
  rcases hc : decodeChars c with _ | cs
  · rw [hc] at h; simp at h
  · rw [hc] at h; simp only [Option.map] at h; injection h with h
    have hcc := decodeChars_inj hc
    subst h; rw [hcc]
    simp only [strCodeM, String.toList_ofList]

/-- Inyectividad de `decodeTerm`/`decodeTerms` (mutua, vía el principio de inducción funcional
    `decodeTerm.induct` — el `motive_2` es la inyectividad de `decodeTerms`). -/
theorem decodeTerm_inj {c t : Term} (h : decodeTerm c = some t) : c = termCodeM t := by
  induction c using decodeTerm.induct
    (motive_2 := fun c => ∀ {ts : List Term}, decodeTerms c = some ts → c = termsCodeM ts)
    generalizing t with
  | case1 cs hd hcs c2 hn c3 hnat hg =>
      unfold decodeTerm at h; rw [hnat, hcs] at h; simp only [if_true, hg] at h
      rcases hnn : decodeNat hn with _ | vn
      · rw [hnn] at h; simp at h
      · rw [hnn] at h; simp only [Option.map] at h; injection h with h; subst h
        have e1 := decodeNat_inj hnat; have e2 := decodeNat_inj hnn; have hcs' := eq_of_beq hcs
        simp only [Bool.and_eq_true, beq_iff_eq] at hg; obtain ⟨hc2, hc3⟩ := hg
        subst e1 e2 hc2 hc3 hcs'; simp only [termCodeM, cons, nil, zero]
  | case2 cs hd hcs c2 hn c3 hnat hg =>
      unfold decodeTerm at h; rw [hnat, hcs] at h; rw [Bool.not_eq_true] at hg
      simp only [if_true, hg] at h; simp at h
  | case3 cs hd hcs c2 hs c3 hts c4 hnat hg ih =>
      unfold decodeTerm at h; rw [hnat, hcs] at h; simp only [if_true, hg] at h
      rcases hstr : decodeStr hs with _ | s
      · rw [hstr] at h; simp at h
      · rw [hstr] at h; simp only [Option.bind] at h
        rcases hts' : decodeTerms hts with _ | ts
        · rw [hts'] at h; simp at h
        · rw [hts'] at h; simp only [Option.map] at h; injection h with h; subst h
          have e1 := decodeNat_inj hnat; have e2 := decodeStr_inj hstr; have e3 := ih hts'
          have hcs' := eq_of_beq hcs
          simp only [Bool.and_eq_true, beq_iff_eq] at hg; obtain ⟨⟨hc2, hc3⟩, hc4⟩ := hg
          subst e1 e2 e3 hc2 hc3 hc4 hcs'; simp only [termCodeM, cons, nil, zero]
  | case4 cs hd hcs c2 hs c3 hts c4 hnat hg =>
      unfold decodeTerm at h; rw [hnat, hcs] at h; rw [Bool.not_eq_true] at hg
      simp only [if_true, hg] at h; simp at h
  | case5 cs hd tl hcons hne0 hne1 =>
      unfold decodeTerm at h; rw [hcons] at h; simp only [if_true] at h; simp at h
  | case6 cs hd tl hcons =>
      unfold decodeTerm at h; rw [Bool.not_eq_true] at hcons; rw [hcons] at h; simp at h
  | case7 c hne =>
      cases c with
      | var n => unfold decodeTerm at h; simp at h
      | func s args =>
          match args, h with
          | [], h => unfold decodeTerm at h; simp at h
          | [_], h => unfold decodeTerm at h; simp at h
          | [a, b], h => exact absurd rfl (hne s a b)
          | _ :: _ :: _ :: _, h => unfold decodeTerm at h; simp at h
  | case8 s hs =>
      rename_i ts hDT; unfold decodeTerms at hDT; rw [hs] at hDT; simp only [if_true] at hDT
      injection hDT with hDT; subst hDT; have := eq_of_beq hs; subst this; rfl
  | case9 s hs =>
      rename_i ts hDT; unfold decodeTerms at hDT; rw [Bool.not_eq_true] at hs; rw [hs] at hDT; simp at hDT
  | case10 s hd tl hs ih1 ih2 =>
      rename_i ts hDT; unfold decodeTerms at hDT; rw [hs] at hDT; simp only [if_true] at hDT
      rcases hh : decodeTerm hd with _ | x
      · rw [hh] at hDT; simp at hDT
      · rw [hh] at hDT; simp only [Option.bind] at hDT
        rcases ht : decodeTerms tl with _ | xs
        · rw [ht] at hDT; simp at hDT
        · rw [ht] at hDT; simp only [Option.map] at hDT; injection hDT with hDT; subst hDT
          have e1 := ih1 hh; have e2 := ih2 ht; have := eq_of_beq hs
          subst e1 e2 this; simp only [termsCodeM, cons]
  | case11 s hd tl hs =>
      rename_i ts hDT; unfold decodeTerms at hDT; rw [Bool.not_eq_true] at hs; rw [hs] at hDT; simp at hDT
  | case12 c hne0 hne1 =>
      rename_i ts hDT
      cases c with
      | var n => unfold decodeTerms at hDT; simp at hDT
      | func s args =>
          match args, hDT with
          | [], hDT => exact absurd rfl (hne0 s)
          | [_, _], hDT => exact absurd rfl (hne1 s _ _)
          | [_], hDT => unfold decodeTerms at hDT; simp at hDT
          | _ :: _ :: _ :: _, hDT => unfold decodeTerms at hDT; simp at hDT

/-- Inyectividad de `decodeTerms` (companion; reusa `decodeTerm_inj`, `motive_1` trivial). -/
theorem decodeTerms_inj {c : Term} {ts : List Term} (h : decodeTerms c = some ts) :
    c = termsCodeM ts := by
  induction c using decodeTerms.induct (motive_1 := fun _ => True) generalizing ts with
  | case1 => trivial
  | case2 => trivial
  | case3 => trivial
  | case4 => trivial
  | case5 => trivial
  | case6 => trivial
  | case7 => trivial
  | case8 s hs =>
      unfold decodeTerms at h; rw [hs] at h; simp only [if_true] at h
      injection h with h; subst h; have := eq_of_beq hs; subst this; rfl
  | case9 s hs =>
      unfold decodeTerms at h; rw [Bool.not_eq_true] at hs; rw [hs] at h; simp at h
  | case10 s hd tl hs ih1 ih2 =>
      unfold decodeTerms at h; rw [hs] at h; simp only [if_true] at h
      rcases hh : decodeTerm hd with _ | x
      · rw [hh] at h; simp at h
      · rw [hh] at h; simp only [Option.bind] at h
        rcases ht : decodeTerms tl with _ | xs
        · rw [ht] at h; simp at h
        · rw [ht] at h; simp only [Option.map] at h; injection h with h; subst h
          have e1 := decodeTerm_inj hh; have e2 := ih2 ht; have := eq_of_beq hs
          subst e1 e2 this; simp only [termsCodeM, cons]
  | case11 s hd tl hs =>
      unfold decodeTerms at h; rw [Bool.not_eq_true] at hs; rw [hs] at h; simp at h
  | case12 c hne0 hne1 =>
      cases c with
      | var n => unfold decodeTerms at h; simp at h
      | func s args =>
          match args, h with
          | [], h => exact absurd rfl (hne0 s)
          | [_, _], h => exact absurd rfl (hne1 s _ _)
          | [_], h => unfold decodeTerms at h; simp at h
          | _ :: _ :: _ :: _, h => unfold decodeTerms at h; simp at h

end ROBINSON_PlusPlus.Meta.CodeDecode

export ROBINSON_PlusPlus.Meta.CodeDecode (
  decodeNat decodeNat_numeralM decodeNat_inj
  decodeChars decodeStr decodeChars_charsCodeM decodeStr_strCodeM decodeChars_inj decodeStr_inj
  decodeTerm decodeTerms decodeTerm_termCodeM decodeTerms_termsCodeM decodeTerm_inj decodeTerms_inj
  decodeForm decodeForm_formCodeM
)

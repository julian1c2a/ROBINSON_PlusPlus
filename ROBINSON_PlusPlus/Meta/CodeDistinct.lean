/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.CodeArith
import ROBINSON_PlusPlus.Meta.Provability
import ROBINSON_PlusPlus.Minimal.Theorems.Block6

import FOL.FOL
import FOL.Theorems.Eq
import FOL.Theorems.Neg
import FOL.Theorems.Derived

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.CodeArith
open ROBINSON_PlusPlus.Minimal.Theorems.Block6

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Meta.CodeDistinct

/-!
## META — NIVEL D (real): aritmética NEGATIVA de códigos  (Fase 2.6, cimientos)

La dirección negativa (reflexión / D3 / `⊬¬G`) reposa sobre que la teoría
**refuta** igualdades de códigos distintos: la contraparte object-level de
`formCode_injective`. Aquí se construyen los primitivos de distinción
(`cons_ne_head`/`cons_ne_tail`/`neg_symm`) y, sobre ellos, `formCode_ne`
(refutación de igualdad de códigos de fórmulas distintas) por inducción meta.

**Alcance honesto:** el resultado «titular» `⊢ ¬provCodeC φ` para `φ`
indemostrable es **Π₁** (`∀p, ¬In ⌜φ⌝ (validProofFn nil p)`) y requiere el
**esquema de inducción** (Fase 5); esto es solo el cimiento aritmético.
-/

/-- Simetría de la refutación de igualdad. -/
theorem neg_symm {a b : Term} (h : axioms ⊢ neg (a =eq b)) : axioms ⊢ neg (b =eq a) :=
  imp_intro (fun hba => mp h (FOL.derive_eq_symm hba))

/-- Si las cabezas son refutablemente distintas, los `cons` lo son. -/
theorem cons_ne_head {h h' t t' : Term} (hh : axioms ⊢ neg (h =eq h')) :
    axioms ⊢ neg (cons h t =eq cons h' t') :=
  imp_intro (fun heq => mp hh (Minimal.Axioms.and_elim_left (mp cons_inj heq)))

/-- Si las colas son refutablemente distintas, los `cons` lo son. -/
theorem cons_ne_tail {h h' t t' : Term} (ht : axioms ⊢ neg (t =eq t')) :
    axioms ⊢ neg (cons h t =eq cons h' t') :=
  imp_intro (fun heq => mp ht (Minimal.Axioms.and_elim_right (mp cons_inj heq)))

/-- `nil` y `cons` son refutablemente distintos (cualquier orden). -/
theorem nil_ne_cons (h t : Term) : axioms ⊢ neg (nil =eq cons h t) :=
  neg_symm (cons_neq_nil h t)

/-! ### `formCode_ne`: la teoría refuta igualdad de códigos de fórmulas distintas -/

/-- Inyectividad de `Char.toNat` (vía `Char.ofNat_toNat`). -/
theorem charToNat_ne {c c' : Char} (h : c ≠ c') : c.toNat ≠ c'.toNat := by
  intro he
  apply h
  have key : Char.ofNat c.toNat = Char.ofNat c'.toNat := by rw [he]
  rwa [Char.ofNat_toNat, Char.ofNat_toNat] at key

/-- `charsCode` distingue listas de caracteres distintas. -/
theorem charsCode_ne : ∀ {cs cs' : List Char}, cs ≠ cs' →
    axioms ⊢ neg (charsCode cs =eq charsCode cs')
  | [], [], h => absurd rfl h
  | [], _ :: _, _ => nil_ne_cons _ _
  | _ :: _, [], _ => cons_neq_nil _ _
  | c :: r, c' :: r', h => by
      by_cases hc : c = c'
      · subst hc
        exact cons_ne_tail (charsCode_ne (fun hrr => h (by rw [hrr])))
      · exact cons_ne_head (gnum_ne (charToNat_ne hc))

/-- `strCode` distingue símbolos distintos. -/
theorem strCode_ne {s s' : String} (h : s ≠ s') : axioms ⊢ neg (strCode s =eq strCode s') :=
  charsCode_ne (fun hl => h (String.toList_inj.mp hl))

mutual
/-- `termCode` distingue términos distintos. -/
theorem termCode_ne : ∀ {t t' : Term}, t ≠ t' → axioms ⊢ neg (termCode t =eq termCode t')
  | .var n, .var m, h => by
      have : n ≠ m := fun hnm => h (by rw [hnm])
      exact cons_ne_tail (cons_ne_head (gnum_ne this))
  | .var _, .func _ _, _ => cons_ne_head (gnum_ne (by decide))
  | .func _ _, .var _, _ => cons_ne_head (gnum_ne (by decide))
  | .func s ts, .func s' ts', h => by
      by_cases hs : s = s'
      · subst hs
        exact cons_ne_tail (cons_ne_tail (cons_ne_head (termsCode_ne (fun ht => h (by rw [ht])))))
      · exact cons_ne_tail (cons_ne_head (strCode_ne hs))
/-- `termsCode` distingue listas de términos distintas. -/
theorem termsCode_ne : ∀ {ts ts' : List Term}, ts ≠ ts' →
    axioms ⊢ neg (termsCode ts =eq termsCode ts')
  | [], [], h => absurd rfl h
  | [], _ :: _, _ => nil_ne_cons _ _
  | _ :: _, [], _ => cons_neq_nil _ _
  | t :: r, t' :: r', h => by
      by_cases ht : t = t'
      · subst ht
        exact cons_ne_tail (termsCode_ne (fun hrr => h (by rw [hrr])))
      · exact cons_ne_head (termCode_ne ht)
end

/-- **Aritmética negativa de códigos**: la teoría refuta la igualdad de códigos de
    fórmulas distintas (contraparte object-level de `formCode_injective`). -/
theorem formCode_ne : ∀ {A B : Formula}, A ≠ B → axioms ⊢ neg (formCode A =eq formCode B)
  | .bottom, .bottom, h => absurd rfl h
  | .atom p ts, .atom p' ts', h => by
      by_cases hp : p = p'
      · subst hp
        exact cons_ne_tail (cons_ne_tail (cons_ne_head (termsCode_ne (fun ht => h (by rw [ht])))))
      · exact cons_ne_tail (cons_ne_head (strCode_ne hp))
  | .eq t u, .eq t' u', h => by
      by_cases ht : t = t'
      · subst ht
        exact cons_ne_tail (cons_ne_tail (cons_ne_head (termCode_ne (fun hu => h (by rw [hu])))))
      · exact cons_ne_tail (cons_ne_head (termCode_ne ht))
  | .impl a b, .impl a' b', h => by
      by_cases ha : a = a'
      · subst ha
        exact cons_ne_tail (cons_ne_tail (cons_ne_head (formCode_ne (fun hb => h (by rw [hb])))))
      · exact cons_ne_tail (cons_ne_head (formCode_ne ha))
  | .and a b, .and a' b', h => by
      by_cases ha : a = a'
      · subst ha
        exact cons_ne_tail (cons_ne_tail (cons_ne_head (formCode_ne (fun hb => h (by rw [hb])))))
      · exact cons_ne_tail (cons_ne_head (formCode_ne ha))
  | .or a b, .or a' b', h => by
      by_cases ha : a = a'
      · subst ha
        exact cons_ne_tail (cons_ne_tail (cons_ne_head (formCode_ne (fun hb => h (by rw [hb])))))
      · exact cons_ne_tail (cons_ne_head (formCode_ne ha))
  | Formula.forall a, Formula.forall a', h =>
      cons_ne_tail (cons_ne_head (formCode_ne (fun ha => h (by rw [ha]))))
  | .ex a, .ex a', h =>
      cons_ne_tail (cons_ne_head (formCode_ne (fun ha => h (by rw [ha]))))
  -- Pares de constructores distintos: las etiquetas numéricas difieren.
  | .bottom, .atom _ _, _ => cons_ne_head (gnum_ne (by decide))
  | .bottom, .eq _ _, _ => cons_ne_head (gnum_ne (by decide))
  | .bottom, .impl _ _, _ => cons_ne_head (gnum_ne (by decide))
  | .bottom, Formula.forall _, _ => cons_ne_head (gnum_ne (by decide))
  | .bottom, .and _ _, _ => cons_ne_head (gnum_ne (by decide))
  | .bottom, .or _ _, _ => cons_ne_head (gnum_ne (by decide))
  | .bottom, .ex _, _ => cons_ne_head (gnum_ne (by decide))
  | .atom _ _, .bottom, _ => cons_ne_head (gnum_ne (by decide))
  | .atom _ _, .eq _ _, _ => cons_ne_head (gnum_ne (by decide))
  | .atom _ _, .impl _ _, _ => cons_ne_head (gnum_ne (by decide))
  | .atom _ _, Formula.forall _, _ => cons_ne_head (gnum_ne (by decide))
  | .atom _ _, .and _ _, _ => cons_ne_head (gnum_ne (by decide))
  | .atom _ _, .or _ _, _ => cons_ne_head (gnum_ne (by decide))
  | .atom _ _, .ex _, _ => cons_ne_head (gnum_ne (by decide))
  | .eq _ _, .bottom, _ => cons_ne_head (gnum_ne (by decide))
  | .eq _ _, .atom _ _, _ => cons_ne_head (gnum_ne (by decide))
  | .eq _ _, .impl _ _, _ => cons_ne_head (gnum_ne (by decide))
  | .eq _ _, Formula.forall _, _ => cons_ne_head (gnum_ne (by decide))
  | .eq _ _, .and _ _, _ => cons_ne_head (gnum_ne (by decide))
  | .eq _ _, .or _ _, _ => cons_ne_head (gnum_ne (by decide))
  | .eq _ _, .ex _, _ => cons_ne_head (gnum_ne (by decide))
  | .impl _ _, .bottom, _ => cons_ne_head (gnum_ne (by decide))
  | .impl _ _, .atom _ _, _ => cons_ne_head (gnum_ne (by decide))
  | .impl _ _, .eq _ _, _ => cons_ne_head (gnum_ne (by decide))
  | .impl _ _, Formula.forall _, _ => cons_ne_head (gnum_ne (by decide))
  | .impl _ _, .and _ _, _ => cons_ne_head (gnum_ne (by decide))
  | .impl _ _, .or _ _, _ => cons_ne_head (gnum_ne (by decide))
  | .impl _ _, .ex _, _ => cons_ne_head (gnum_ne (by decide))
  | Formula.forall _, .bottom, _ => cons_ne_head (gnum_ne (by decide))
  | Formula.forall _, .atom _ _, _ => cons_ne_head (gnum_ne (by decide))
  | Formula.forall _, .eq _ _, _ => cons_ne_head (gnum_ne (by decide))
  | Formula.forall _, .impl _ _, _ => cons_ne_head (gnum_ne (by decide))
  | Formula.forall _, .and _ _, _ => cons_ne_head (gnum_ne (by decide))
  | Formula.forall _, .or _ _, _ => cons_ne_head (gnum_ne (by decide))
  | Formula.forall _, .ex _, _ => cons_ne_head (gnum_ne (by decide))
  | .and _ _, .bottom, _ => cons_ne_head (gnum_ne (by decide))
  | .and _ _, .atom _ _, _ => cons_ne_head (gnum_ne (by decide))
  | .and _ _, .eq _ _, _ => cons_ne_head (gnum_ne (by decide))
  | .and _ _, .impl _ _, _ => cons_ne_head (gnum_ne (by decide))
  | .and _ _, Formula.forall _, _ => cons_ne_head (gnum_ne (by decide))
  | .and _ _, .or _ _, _ => cons_ne_head (gnum_ne (by decide))
  | .and _ _, .ex _, _ => cons_ne_head (gnum_ne (by decide))
  | .or _ _, .bottom, _ => cons_ne_head (gnum_ne (by decide))
  | .or _ _, .atom _ _, _ => cons_ne_head (gnum_ne (by decide))
  | .or _ _, .eq _ _, _ => cons_ne_head (gnum_ne (by decide))
  | .or _ _, .impl _ _, _ => cons_ne_head (gnum_ne (by decide))
  | .or _ _, Formula.forall _, _ => cons_ne_head (gnum_ne (by decide))
  | .or _ _, .and _ _, _ => cons_ne_head (gnum_ne (by decide))
  | .or _ _, .ex _, _ => cons_ne_head (gnum_ne (by decide))
  | .ex _, .bottom, _ => cons_ne_head (gnum_ne (by decide))
  | .ex _, .atom _ _, _ => cons_ne_head (gnum_ne (by decide))
  | .ex _, .eq _ _, _ => cons_ne_head (gnum_ne (by decide))
  | .ex _, .impl _ _, _ => cons_ne_head (gnum_ne (by decide))
  | .ex _, Formula.forall _, _ => cons_ne_head (gnum_ne (by decide))
  | .ex _, .and _ _, _ => cons_ne_head (gnum_ne (by decide))
  | .ex _, .or _ _, _ => cons_ne_head (gnum_ne (by decide))

end ROBINSON_PlusPlus.Meta.CodeDistinct

export ROBINSON_PlusPlus.Meta.CodeDistinct (
  neg_symm
  cons_ne_head
  cons_ne_tail
  nil_ne_cons
  charsCode_ne
  strCode_ne
  termCode_ne
  termsCode_ne
  formCode_ne
)

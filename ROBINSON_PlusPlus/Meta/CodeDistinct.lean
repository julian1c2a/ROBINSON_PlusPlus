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

**⚠️ CORRECCIÓN 2026‑07‑13 (auditoría).** Aquí se decía que el resultado «titular»
`⊢ ¬provCodeC φ` para `φ` indemostrable (Π₁, `∀p. ¬In ⌜φ⌝ (…)`) se obtendría con
el **esquema de inducción** (Fase 5). **Ese plan es IMPOSIBLE**: para `φ = ⊥`
—indemostrable si la teoría es consistente— `⊢ ¬provCodeC ⊥` es **literalmente
`Con(T)`**, que por **Gödel II** la teoría NO demuestra. (Para `φ = G` tampoco: por
el punto fijo, `⊢ ¬provCodeC' G` ⟺ `⊢ G`, y `⊬ G`.) La vía «la teoría refuta la
demostrabilidad» está **cerrada por Gödel**, no por falta de trabajo.

**Alcance honesto (real).** Este módulo es el cimiento aritmético de la dirección
negativa, pero ésta **sólo puede cerrarse a nivel META**: la **reflexión**
(`(axioms ⊢ provCodeC' φ) → Prf φ`) es una hipótesis meta —la ω‑consistencia
clásica— y así se enuncia, **explícita**, en `Meta/DiagonalTwo.lean`
(`Reflects` / `goedel_first_undecidable_real'`). Descargarla exige ω‑consistencia
**+ Δ₀‑completitud NEGATIVA del verificador en testigos CONCRETOS** (cerrados) —
el espejo de `repr_pos'`, y sí alcanzable, a diferencia de la versión Π₁ universal.
`formCode_ne` es la base de eso.
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

/-! ### 🏁 Códigos de FÓRMULA contra códigos de TÉRMINO — la causa (f) de `DEUDA_chainNeg`

⭐⭐ `StdArgs` (`Meta/OmegaReflect.lean:148`) sólo exige que cada argumento sea `formCode _`
**o** `termCode _`, **sin decir cuál**. Por eso una línea estándar puede llevar un código de
término donde el tag espera uno de fórmula, y entonces `decodeForm` falla: ésa es la **sexta**
causa de rechazo del decodificador (ADR‑075).

⭐ Lo que la cierra es puro **álgebra de códigos**, y se apoya en un hecho de una línea: los tags
de cabeza son **disjuntos** — `termCode` usa 0/1 y `formCode` usa 2…9.

🔑 *La mitad cara aparente —«¿y si el tag SÍ coincide?»— sólo ocurre en un constructor por lema,
y ahí se desciende una capa y se vuelve al mismo hecho de una línea.* -/

/-- El TAG de cabeza del código de una fórmula. -/
def formTag : Formula → Nat
  | .bottom => 2 | .atom _ _ => 3 | .eq _ _ => 4 | .impl _ _ => 5
  | Formula.forall _ => 6 | .and _ _ => 7 | .or _ _ => 8 | .ex _ => 9

theorem formCode_eq_cons (f : Formula) : ∃ r, formCode f = cons (numeral (formTag f)) r := by
  cases f <;> exact ⟨_, rfl⟩

/-- ⭐ **La mitad UNIFORME de (f)**: si el tag de cabeza no coincide, la teoría los separa. -/
theorem formCode_ne_cons_of_tag (f : Formula) {n : Nat} (r : Term) (h : formTag f ≠ n) :
    axioms ⊢ neg (formCode f =eq cons (numeral n) r) := by
  obtain ⟨r', hr⟩ := formCode_eq_cons f
  rw [hr]
  exact cons_ne_head (gnum_ne h)

/-- El TAG de cabeza del código de un término. Gemelo de `formTag`. -/
def termTag : Term → Nat
  | .var _ => 0 | .func _ _ => 1

theorem termCode_eq_cons (t : Term) : ∃ r, termCode t = cons (numeral (termTag t)) r := by
  cases t <;> exact ⟨_, rfl⟩

/-- ⭐ Gemelo de `formCode_ne_cons_of_tag` para el sort TÉRMINO. Lo consume el refutador de la
    guarda `hasWitF`: `isFormCodeE2` son ocho formas con cabezas 2…9, y un `termCode` tiene
    cabeza 0 o 1. -/
theorem termCode_ne_cons_of_tag (t : Term) {n : Nat} (r : Term) (h : termTag t ≠ n) :
    axioms ⊢ neg (termCode t =eq cons (numeral n) r) := by
  obtain ⟨r', hr⟩ := termCode_eq_cons t
  rw [hr]
  exact cons_ne_head (gnum_ne h)

/-- ⭐ **La pieza base de (f)**: un código de FÓRMULA nunca es un código de TÉRMINO. -/
theorem formCode_ne_termCode (A : Formula) (t : Term) :
    axioms ⊢ neg (formCode A =eq termCode t) := by
  cases A <;> cases t <;> exact cons_ne_head (gnum_ne (by decide))

theorem termCode_ne_formCode (t : Term) (A : Formula) :
    axioms ⊢ neg (termCode t =eq formCode A) := neg_symm (formCode_ne_termCode A t)

/-! Las **ranuras**: un `termCode` donde va un código de FÓRMULA, y al revés. Una por posición
de argumento de cada constructor que `tagConcl` usa para reconstruir la conclusión. -/

theorem formCode_ne_implc_tc_1 (f : Formula) (u X : Term) :
    axioms ⊢ neg (formCode f =eq implc (termCode u) X) := by
  cases f with
  | impl a b => exact cons_ne_tail (cons_ne_head (formCode_ne_termCode a u))
  | _ => exact formCode_ne_cons_of_tag _ (n := 5) _ (by simp only [formTag]; decide)

theorem formCode_ne_implc_tc_2 (f : Formula) (u X : Term) :
    axioms ⊢ neg (formCode f =eq implc X (termCode u)) := by
  cases f with
  | impl a b =>
      exact cons_ne_tail (cons_ne_tail (cons_ne_head (formCode_ne_termCode b u)))
  | _ => exact formCode_ne_cons_of_tag _ (n := 5) _ (by simp only [formTag]; decide)

theorem formCode_ne_andc_tc_1 (f : Formula) (u X : Term) :
    axioms ⊢ neg (formCode f =eq andc (termCode u) X) := by
  cases f with
  | and a b => exact cons_ne_tail (cons_ne_head (formCode_ne_termCode a u))
  | _ => exact formCode_ne_cons_of_tag _ (n := 7) _ (by simp only [formTag]; decide)

theorem formCode_ne_orc_tc_1 (f : Formula) (u X : Term) :
    axioms ⊢ neg (formCode f =eq orc (termCode u) X) := by
  cases f with
  | or a b => exact cons_ne_tail (cons_ne_head (formCode_ne_termCode a u))
  | _ => exact formCode_ne_cons_of_tag _ (n := 8) _ (by simp only [formTag]; decide)

theorem formCode_ne_forallc_tc (f : Formula) (u : Term) :
    axioms ⊢ neg (formCode f =eq forallc (termCode u)) := by
  cases f with
  | «forall» a => exact cons_ne_tail (cons_ne_head (formCode_ne_termCode a u))
  | _ => exact formCode_ne_cons_of_tag _ (n := 6) _ (by simp only [formTag]; decide)

theorem formCode_ne_exc_tc (f : Formula) (u : Term) :
    axioms ⊢ neg (formCode f =eq exc (termCode u)) := by
  cases f with
  | ex a => exact cons_ne_tail (cons_ne_head (formCode_ne_termCode a u))
  | _ => exact formCode_ne_cons_of_tag _ (n := 9) _ (by simp only [formTag]; decide)

/-- ⚠️ El desajuste **INVERSO**: un código de FÓRMULA donde va un término (`eqc`, tag 12).
No es simétrico del anterior por accidente: es la otra mitad de (f), y hay que enunciarla. -/
theorem formCode_ne_eqc_fc_1 (f : Formula) (A : Formula) (X : Term) :
    axioms ⊢ neg (formCode f =eq eqc (formCode A) X) := by
  cases f with
  | eq t1 t2 => exact cons_ne_tail (cons_ne_head (termCode_ne_formCode t1 A))
  | _ => exact formCode_ne_cons_of_tag _ (n := 4) _ (by simp only [formTag]; decide)



/-! ### ⭐⭐⭐ UN SOLO REFUTADOR para toda la causa (f) transparente

⚠️ Antes de esto, cada tag y cada ranura pedía su propio lema: `formCode_ne_implc_tc_1`,
`_tc_2`, `_andc_tc_1`, … y el ensamblaje por tag encima. Contados: **~32**.

⭐ `NotFC e` dice «este término **no es el código de ninguna fórmula**», por razones puramente
**sintácticas**: o es un código de término, o lleva uno en una posición donde va un código de
fórmula. Es un inductivo de **nueve** constructores, y `formCode_ne_notFC` lo refuta **de una
vez para todos**.

⇒ el refutador de cada tag y cada ranura pasa a ser **una derivación de una línea**:

    -- tag 0, ranura 2:  implc a (implc (termCode u) a)
    formCode_ne_notFC (NotFC.implcR _ (NotFC.implcL _ (NotFC.tc u))) f

🔑 *Cuando los refutadores de una familia se COMPONEN (ADR‑094), la composición ya es un
inductivo esperando a que lo escriban.* Los lemas sueltos de arriba se quedan como los casos
base que el inductivo usa y como ejemplos trabajados.

⛔ **Su límite, medido**: sólo alcanza las posiciones **TRANSPARENTES**, las construidas con
`implc`/`andc`/`orc`/`forallc`/`exc`. De las ~32 ranuras, **tres** caen dentro de `substfc` —
el argumento de término de los tags 9 y 10, y el de fórmula del 13— y ésas **no se refutan por
la sintaxis**: van por las guardas que ADR‑020 metió dentro de `lineWF`.

⭐⭐ **Y la otra mitad**: `NotTC e` dice «este término **no es el código de ningún término**».
Hace falta porque (f) tiene **dos direcciones** —`termCode` donde va fórmula, y `formCode` donde
va término (tags 12 y 13)— y `eqc` es la única constructora transparente que abre un hueco de
TÉRMINO. Por eso `NotFC` gana dos constructoras `eqc*` que consumen un `NotTC`.

⚠️ `NotTC` tiene **una sola** constructora, y eso es deliberado: es lo que hace falta, medido.
Crecerá si aparece una posición de término transparente más. -/
inductive NotTC : Term → Prop
  | fc (A : Formula) : NotTC (formCode A)

theorem termCode_ne_notTC : ∀ {e : Term}, NotTC e → ∀ t : Term,
    axioms ⊢ neg (termCode t =eq e)
  | _, NotTC.fc A, t => termCode_ne_formCode t A

inductive NotFC : Term → Prop
  | tc (u : Term) : NotFC (termCode u)
  | eqcL {a : Term} (b : Term) : NotTC a → NotFC (eqc a b)
  | eqcR (a : Term) {b : Term} : NotTC b → NotFC (eqc a b)
  | implcL {a : Term} (b : Term) : NotFC a → NotFC (implc a b)
  | implcR (a : Term) {b : Term} : NotFC b → NotFC (implc a b)
  | andcL {a : Term} (b : Term) : NotFC a → NotFC (andc a b)
  | andcR (a : Term) {b : Term} : NotFC b → NotFC (andc a b)
  | orcL {a : Term} (b : Term) : NotFC a → NotFC (orc a b)
  | orcR (a : Term) {b : Term} : NotFC b → NotFC (orc a b)
  | forallcI {a : Term} : NotFC a → NotFC (forallc a)
  | excI {a : Term} : NotFC a → NotFC (exc a)

theorem formCode_ne_notFC : ∀ {e : Term}, NotFC e → ∀ f : Formula,
    axioms ⊢ neg (formCode f =eq e)
  | _, NotFC.tc u, f => formCode_ne_termCode f u
  | _, NotFC.eqcL b h, f => by
      cases f with
      | eq x y => exact cons_ne_tail (cons_ne_head (termCode_ne_notTC h x))
      | _ => exact formCode_ne_cons_of_tag _ (n := 4) _ (by simp only [formTag]; decide)
  | _, NotFC.eqcR a h, f => by
      cases f with
      | eq x y =>
          exact cons_ne_tail (cons_ne_tail (cons_ne_head (termCode_ne_notTC h y)))
      | _ => exact formCode_ne_cons_of_tag _ (n := 4) _ (by simp only [formTag]; decide)
  | _, NotFC.implcL b h, f => by
      cases f with
      | impl x y => exact cons_ne_tail (cons_ne_head (formCode_ne_notFC h x))
      | _ => exact formCode_ne_cons_of_tag _ (n := 5) _ (by simp only [formTag]; decide)
  | _, NotFC.implcR a h, f => by
      cases f with
      | impl x y =>
          exact cons_ne_tail (cons_ne_tail (cons_ne_head (formCode_ne_notFC h y)))
      | _ => exact formCode_ne_cons_of_tag _ (n := 5) _ (by simp only [formTag]; decide)
  | _, NotFC.andcL b h, f => by
      cases f with
      | and x y => exact cons_ne_tail (cons_ne_head (formCode_ne_notFC h x))
      | _ => exact formCode_ne_cons_of_tag _ (n := 7) _ (by simp only [formTag]; decide)
  | _, NotFC.andcR a h, f => by
      cases f with
      | and x y =>
          exact cons_ne_tail (cons_ne_tail (cons_ne_head (formCode_ne_notFC h y)))
      | _ => exact formCode_ne_cons_of_tag _ (n := 7) _ (by simp only [formTag]; decide)
  | _, NotFC.orcL b h, f => by
      cases f with
      | or x y => exact cons_ne_tail (cons_ne_head (formCode_ne_notFC h x))
      | _ => exact formCode_ne_cons_of_tag _ (n := 8) _ (by simp only [formTag]; decide)
  | _, NotFC.orcR a h, f => by
      cases f with
      | or x y =>
          exact cons_ne_tail (cons_ne_tail (cons_ne_head (formCode_ne_notFC h y)))
      | _ => exact formCode_ne_cons_of_tag _ (n := 8) _ (by simp only [formTag]; decide)
  | _, NotFC.forallcI h, f => by
      cases f with
      | «forall» x => exact cons_ne_tail (cons_ne_head (formCode_ne_notFC h x))
      | _ => exact formCode_ne_cons_of_tag _ (n := 6) _ (by simp only [formTag]; decide)
  | _, NotFC.excI h, f => by
      cases f with
      | ex x => exact cons_ne_tail (cons_ne_head (formCode_ne_notFC h x))
      | _ => exact formCode_ne_cons_of_tag _ (n := 9) _ (by simp only [formTag]; decide)

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
  formTag formCode_eq_cons formCode_ne_cons_of_tag
  termTag termCode_eq_cons termCode_ne_cons_of_tag
  formCode_ne_termCode termCode_ne_formCode
  formCode_ne_implc_tc_1 formCode_ne_implc_tc_2
  formCode_ne_andc_tc_1 formCode_ne_orc_tc_1
  formCode_ne_forallc_tc formCode_ne_exc_tc formCode_ne_eqc_fc_1
  NotFC formCode_ne_notFC
  NotFC.tc NotFC.implcL NotFC.implcR NotFC.andcL NotFC.andcR
  NotFC.orcL NotFC.orcR NotFC.forallcI NotFC.excI
  NotTC termCode_ne_notTC NotTC.fc NotFC.eqcL NotFC.eqcR
)

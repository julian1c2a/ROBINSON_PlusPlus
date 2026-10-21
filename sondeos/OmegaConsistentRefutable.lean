/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus

/-!
# SONDEO · L1‑4 — `OmegaConsistent` es refutable por su propia DEFINICIÓN (2026‑10‑02)

**Pregunta** (auditoría de la base, ronda 1, L1‑4): ¿puede valer la hipótesis de la mitad `⊬¬G`?
`OmegaConsistent` (`Meta/OmegaReflect.lean:267`, retirada con ADR‑115) cuantificaba sobre TODA fórmula `A`,
pero sólo con testigos `objList l` de cadenas estándar (`StdChain`, la estrechada de ADR‑022).

## 🏁 Respuesta, COMPILADA: no

Con `A := (#0 = 1)`: `∃A` sale por introducción del `∃` + reflexividad, y para toda cadena estándar
`objList l ≠ 1` (si `l = []` es `nil = 0`; si `l = x :: l'`, `x` es un `cons`, y las monotonías de Cantor
cierran sin evaluar nada). ⇒ la hipótesis es FALSA.

## Registro (compilado el 2026‑10‑02 contra RPP `1dac85a`, antes de la retirada)

Sobre la definición de entonces, en `⊢`:

```lean
theorem not_omega_of (h : ∀ l, StdChain l → axioms ⊢ neg (objList l =eq succ zero)) :
    Not OmegaConsistent                      -- [propext, Classical.choice, Quot.sound]
theorem not_omegaConsistent : Not OmegaConsistent :=
  not_omega_of (fun l hl => prf_to_derives (prf_objList_ne_one l hl))
  -- [propext, Classical.choice, Quot.sound, MetaRules.imp_intro,
  --  ROBINSON_PlusPlus.Full.ax_induction_prim, ROBINSON_PlusPlus.Full.ax_list_induction]
```

⇒ `reflects_of_omega` y `goedel_first_undecidable_omega` eran vacuos por la DEFINICIÓN de su hipótesis, y lo
habrían seguido siendo tras reparar todo lo demás. ADR‑022 vio que la solidez no cubría la clase estrecha,
pero no que la hacía REFUTABLE.

## Hoy (ADR‑115): la misma definición sobre `Prf` también es refutable

`OmegaConsistent`, `prf_to_derives` y toda la capa `⊢` se retiraron el 2026‑10‑02. Lo que se conserva es la
lección, trasladada al cálculo que queda: `OmegaConsistentPrf` es la definición retirada con `Prf` en lugar de
`axioms ⊢`, y `not_omegaConsistentPrf` la refuta con la MISMA prueba, ahora sin nada de `⊢`.

⚠️ Para la mitad `⊬¬G` sobre `Prf`: la ω‑consistencia NO puede enunciarse así. Arreglo propuesto por la
auditoría: restringir al único `∃` que se usa (`OmegaConsistentProv`, sólo `provBody`), o Rosser.
(✏️ 2026‑10‑14, ADR‑134: `⊬¬G` salió sin ω‑consistencia ni Rosser: `goedel_I_neg : ¬ Prf (neg godelCN)`,
`Meta/SolidezVerificador.lean`, ADR‑121, por la solidez del verificador en el modelo `MNV V₀`.)
-/

/-! ## 0 · `StdChain`, copiada TAL CUAL de `Meta/OmegaReflect.lean` (✏️ 2026‑10‑18, ADR‑160)

`Meta/OmegaReflect.lean` salió del build con T66 (ADR‑160; se recupera de la etiqueta `archivo/t66-2026-10-18`). Este
sondeo sólo usa `StdChain`; van aquí ella y sus dos dependencias, en el MISMO espacio de nombres. Y las §1ter y
§1quater de aquel módulo, que son la «Verificación» de la regla M‑8 (DECISIONS.md, la tabla MANDATORIES):
`stdChain_proofCode'` y `junk_line_not_stdLine`. -/

namespace ROBINSON_PlusPlus.Meta.OmegaReflect

open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.ProofChain
open ROBINSON_PlusPlus.Meta.HilbertSeq ROBINSON_PlusPlus.Meta.Hilbert

/-- Los **ARGUMENTOS** de una justificación estándar: la lista‑código formada por códigos de
    fórmula (`formCode`) y de término (`termCode`), que es exactamente lo que produce `lineJustif`. -/
inductive StdArgs : Term → Prop
  | nil : StdArgs nil
  | form {t : Term} (A : Formula) : StdArgs t → StdArgs (cons (formCode A) t)
  | term {t : Term} (u : Term) : StdArgs t → StdArgs (cons (termCode u) t)

/-- Una **LÍNEA ESTÁNDAR**: `⟨⌜f⌝, k̄, args…⟩` — la forma exacta de `lineCode'`. -/
def StdLine (x : Term) : Prop :=
  ∃ (f : Formula) (k : Nat) (as : Term),
    And (x = cons (formCode f) (cons (numeralM k) as)) (StdArgs as)

/-- **Testigos ESTÁNDAR** del `∃` de `provCodeC'`: los términos‑lista `objList l` con **todas sus
    líneas ESTÁNDAR**. -/
def StdChain (l : List Term) : Prop := ∀ x ∈ l, StdLine x

/-! ### 1ter · 🏁 LA GARANTÍA: la clase contiene los códigos de prueba REALES

Sin esto el estrechamiento habría sido una trampa: se podía hacer `NegVerifier` trivial vaciando la
clase, y `OmegaConsistent` se volvía **falsa** (las dos, retiradas con ADR‑115; y `OmegaConsistent`
resultó refutable sin vaciar nada, L1‑4). Lo que sigue lo impedía, y sigue probado. -/

/-- Toda línea producida por `lineCode'` es estándar — los **21 tags**. -/
theorem stdLine_lineCode' (acc : List Formula) (f : Formula) (r : Rule) :
    StdLine (lineCode' acc f r) := by
  cases r with
  | p1 A B => exact ⟨f, 0, _, rfl, .form A (.form B .nil)⟩
  | p2 A B C => exact ⟨f, 1, _, rfl, .form A (.form B (.form C .nil))⟩
  | c1 A B => exact ⟨f, 2, _, rfl, .form A (.form B .nil)⟩
  | c2 A B => exact ⟨f, 3, _, rfl, .form A (.form B .nil)⟩
  | c3 A B => exact ⟨f, 4, _, rfl, .form A (.form B .nil)⟩
  | j1 A B => exact ⟨f, 5, _, rfl, .form A (.form B .nil)⟩
  | j2 A B => exact ⟨f, 6, _, rfl, .form A (.form B .nil)⟩
  | j3 A B C => exact ⟨f, 7, _, rfl, .form A (.form B (.form C .nil))⟩
  | efq A => exact ⟨f, 8, _, rfl, .form A .nil⟩
  | q1 A t => exact ⟨f, 9, _, rfl, .form A (.term t .nil)⟩
  | q2 A t => exact ⟨f, 10, _, rfl, .form A (.term t .nil)⟩
  | q3 A B => exact ⟨f, 11, _, rfl, .form A (.form B .nil)⟩
  | eqrefl t => exact ⟨f, 12, _, rfl, .term t .nil⟩
  | leibniz A t₁ t₂ => exact ⟨f, 13, _, rfl, .form A (.term t₁ (.term t₂ .nil))⟩
  | p3 A => exact ⟨f, 14, _, rfl, .form A .nil⟩
  | thy _ => exact ⟨f, 15, _, rfl, .nil⟩
  | mp _ _ => exact ⟨f, 16, _, rfl, .form _ .nil⟩
  | gen _ => exact ⟨f, 17, _, rfl, .form _ .nil⟩
  | ind A => exact ⟨f, 18, _, rfl, .form A .nil⟩
  | qconf P C => exact ⟨f, 19, _, rfl, .form P (.form C .nil)⟩
  | listInd A => exact ⟨f, 20, _, rfl, .form A .nil⟩

/-- 🏁 **LA GARANTÍA DE ADR‑022**: el código de **cualquier** demostración‑secuencia es un testigo
    estándar. ⇒ estrechar la clase **no deja fuera ningún testigo real**. Era lo único que hacía
    admisible la `OmegaConsistent` reforzada (retirada con ADR‑115, y refutable: L1‑4); el
    teorema vale por sí solo. -/
theorem stdChain_proofCode' : ∀ (rs : List Rule) (acc : List Formula),
    ∃ l : List Term, And (StdChain l) (objList l = proofCode' rs acc) := by
  intro rs
  induction rs with
  | nil => intro acc; exact ⟨[], (by intro x hx; cases hx), rfl⟩
  | cons r rs ih =>
      intro acc
      cases hs : stepConcl acc r with
      | none => exact ⟨[], (by intro x hx; cases hx), (by simp [proofCode', hs]; rfl)⟩
      | some g =>
          obtain ⟨l, hl, hobj⟩ := ih (acc ++ [g])
          refine ⟨lineCode' acc g r :: l, ?_, ?_⟩
          · intro x hx
            cases hx with
            | head => exact stdLine_lineCode' acc g r
            | tail _ h => exact hl _ h
          · show cons (lineCode' acc g r) (objList l) = _
            simp [proofCode', hs, hobj]

/-! ### 1quater · Y EL PAYOFF: la basura que la clase ancha aceptaba queda FUERA -/

theorem formCode_is_cons (A : Formula) : ∃ h t, formCode A = cons h t := by
  cases A <;> exact ⟨_, _, rfl⟩

theorem termCode_is_cons (t : Term) : ∃ h u, termCode t = cons h u := by
  cases t <;> exact ⟨_, _, rfl⟩

theorem cons_ne_numeralM (h t : Term) (n : Nat) : cons h t ≠ numeralM n := by
  cases n <;> simp [cons, numeralM, succ, zero]

theorem stdArgs_head {x : Term} (hx : StdArgs x) :
    Or (x = nil) (∃ hd tl, And (x = cons hd tl)
      (Or (∃ A, hd = formCode A) (∃ u, hd = termCode u))) := by
  cases hx with
  | nil => exact .inl rfl
  | form A _ => exact .inr ⟨_, _, rfl, .inl ⟨A, rfl⟩⟩
  | term u _ => exact .inr ⟨_, _, rfl, .inr ⟨u, rfl⟩⟩

/-- ⛔ **Un NUMERAL PELADO no es un argumento estándar** — y ahí está toda la diferencia con
    `IsCodeShaped`, que sí lo aceptaba. -/
theorem not_stdArgs_numeralM (n : Nat) (as : Term) : ¬ StdArgs (cons (numeralM n) as) := by
  intro h
  rcases stdArgs_head h with hnil | ⟨hd, tl, heq, hcase⟩
  · exact absurd hnil (by simp [cons, nil, zero])
  · have hhd : hd = numeralM n := by
      have h2 := heq; simp [cons] at h2; exact h2.1.symm
    rcases hcase with ⟨A, hA⟩ | ⟨u, hu⟩
    · obtain ⟨a, b, hab⟩ := formCode_is_cons A
      exact cons_ne_numeralM a b n (by rw [← hab, ← hA, hhd])
    · obtain ⟨a, b, hab⟩ := termCode_is_cons u
      exact cons_ne_numeralM a b n (by rw [← hab, ← hu, hhd])

/-- 🏁 **La línea basura de `archivo/sondeos-2026-10:sondeos/MedirF_Censo.lean` §4 queda FUERA de la clase.** Era el
    testigo `StdChain` legítimo cuya refutación exigía evaluar Cantor. -/
theorem junk_line_not_stdLine :
    ¬ StdLine (cons (formCode (Formula.impl Formula.bottom Formula.bottom))
        (cons (numeralM 8) (cons (numeralM 3) nil))) := by
  rintro ⟨f, k, as, heq, has⟩
  have hs : as = cons (numeralM 3) nil := by simp [cons] at heq; exact heq.2.2.symm
  exact not_stdArgs_numeralM 3 nil (hs ▸ has)

end ROBINSON_PlusPlus.Meta.OmegaReflect

open FOL ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.HilbertDeduction ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.NatArithPrf ROBINSON_PlusPlus.Meta.BoundedInPrf ROBINSON_PlusPlus.Meta.CantorMonoPrf
open ROBINSON_PlusPlus.Meta.OmegaReflect ROBINSON_PlusPlus.Meta.ArithPrf

namespace Sondeos.OmegaConsistentRefutable

theorem PrfH_eq_zero_of_lt_one {Γ : List Formula} {x : Term}
    (h : PrfH Γ (lt x (succ zero))) : PrfH Γ (x =eq zero) :=
  PrfH_or_elim (PrfH.mp _ _ _ (prf_to_prfH (prf_lt_succ_split x zero) _) h)
    (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prfᵢ.efq _))
      (PrfH.mp _ _ _ (prf_to_prfH (prf_not_lt_zero x) _) (PrfH.hyp _ _ (List.Mem.head _))))
    (PrfH.hyp _ _ (List.Mem.head _))

/-- `cons (cons F R) T ≠ 1`: `x := cons F R < cons x T = 1` ⇒ `x = 0` ⇒ `R < x = 0`. -/
theorem prf_cons2_ne_one (F R T : Term) : Prf (neg (cons (cons F R) T =eq succ zero)) := by
  refine prf_deduction ?_
  have E := prfH_hyp_self (cons (cons F R) T =eq succ zero)
  have hx := PrfH_eq_zero_of_lt_one
    (PrfH_lt_subst2 E (prf_to_prfH (prf_cantor_mono_left (cons F R) T) _))
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_not_lt_zero R) _)
    (PrfH_lt_subst2 hx (prf_to_prfH (prf_cantor_mono_right F R) _))

theorem prf_objList_ne_one : ∀ l : List Term, StdChain l → Prf (neg (objList l =eq succ zero))
  | [], _ => prf_deduction (PrfH.mp _ _ _ (prf_to_prfH (prf_succ_ne_zero zero) _)
      (PrfH_eq_symm (prfH_hyp_self _)))
  | x :: _, hl => by
      obtain ⟨f, k, as, hx, _⟩ := hl x (List.Mem.head _)
      subst hx; exact prf_cons2_ne_one _ _ _

/-- La definición retirada (`OmegaReflect.lean:267`), con `Prf` en lugar de `axioms ⊢`: los mismos
    testigos, sólo `objList l` de cadenas estándar. -/
def OmegaConsistentPrf : Prop :=
  ∀ A : Formula, Prf (Formula.ex A) →
    ¬ (∀ l : List Term, StdChain l → Prf (neg (substFormula 0 (objList l) A)))

/-- 🏁 Y es REFUTABLE, sobre `Prf` y sin nada de `⊢`. -/
theorem not_omegaConsistentPrf : Not OmegaConsistentPrf := fun hω =>
  hω (Formula.eq (.var 0) (succ zero))
    (prf_ex_intro (succ zero)
      (by simp only [substFormula, substTerm, substTerms, succ, zero, ite_true]; exact prf_refl _))
    (fun l hl => by
      simpa only [substFormula, substTerm, substTerms, succ, zero, ite_true] using prf_objList_ne_one l hl)

end Sondeos.OmegaConsistentRefutable

#print axioms Sondeos.OmegaConsistentRefutable.prf_objList_ne_one
#print axioms Sondeos.OmegaConsistentRefutable.not_omegaConsistentPrf

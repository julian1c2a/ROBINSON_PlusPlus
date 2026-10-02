/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import FOL.FOL
import FOL.MetaRules
import FOL.Finitary0
import ROBINSON_PlusPlus.Full.Lists

/-!
# SONDEO · L1‑3 — los postulados de la capa `⊢` son REFUTABLES (2026‑10‑02)

**Pregunta** (auditoría de la base, ronda 1: L1‑3, L2‑4 y L4‑1): ¿es consistente el entorno que RPP
importa, `FOL.FOL` + `FOL.MetaRules`? La doctrina escrita decía que sí mientras nadie indujera sobre
`Derives` (M‑11; `FOL/AXIOMS.md:293`, `FOL/FOL/Inconsistencia.lean:16-18` y `:66`, ADR‑025: «RPP no está
afectado»).

## 🏁 Respuesta, COMPILADA: no

1. `derives_tval`: los 22 constructores de `Derives` son sólidos para la valuación booleana `tval` de
   `FOL.Finitary0`, por INDUCCIÓN y sin ningún axioma (`[propext, Quot.sound]`). El recursor cubre por
   definición a TODOS los habitantes, también a los que fabrican los `axiom`.
2. ⇒ los ENUNCIADOS de `imp_intro`, `raa` y `ax_list_induction` son FALSOS, y se demuestra sin usarlos
   (§2: `imp_intro_refutable`, `raa_refutable`, `ax_list_induction_refutable`).
3. ⇒ el entorno que los postula demuestra `False` (§3: `imp_intro_false`, `raa_false`,
   `ax_list_induction_false`, cada uno con su axioma en el footprint).

🔑 *El problema nunca fue INDUCIR: el axioma es falso, y el recursor lo demuestra.* M‑11 evitaba ESCRIBIR la
contradicción, no la quitaba. Todo teorema con uno de estos axiomas en el footprint es teorema de una teoría
inconsistente: 53 de las 517 filas de `check-footprints.bash` el 2026‑10‑02 (`negVerifier_proved`,
`derives_completo`, `GodelTwo.d3`, el censo de `coreAxioms`, la librería de `Minimal`/`Full`…).

## Uso como control negativo

Decisión del propietario (2026‑10‑02): la capa `⊢` se retira como capa de trabajo y las meta‑reglas de FOL
se retiran, «no hacemos uso de herramientas que no sean verdaderas». Cuando eso ocurra, la §3 dejará de
compilar y se borra; **la §2 sigue valiendo para siempre**: dice que esos enunciados no se pueden volver a
postular sin hacer inconsistente a Lean.

⚠️ No medido aquí: `or_elim` (con `P ∨ ¬P` pide una derivación del tercio excluso sólo con constructores) y
`ex_elim` (pide un modelo de dos puntos).
-/

open FOL.Finitary0

namespace Sondeos.MetaReglasRefutables

/-! ## §1 · La solidez booleana de los 22 constructores, por inducción y sin axiomas -/

theorem tval_localRule (a : Bool) {s s' : Formula} (h : LocalRule s s') : tval a s' = tval a s := by
  cases h with
  | commuteImpl A B C => simp only [tval]; cases tval a A <;> cases tval a B <;> rfl

theorem tval_replaceAt (a : Bool) (p : Pos) : ∀ (f s s' : Formula),
    getAt? f p = some s → tval a s' = tval a s → tval a (replaceAt f p s') = tval a f := by
  induction p with
  | root => intro f s s' hg hv; simp only [getAt?, Option.some.injEq] at hg; subst hg; simpa [replaceAt] using hv
  | left p ih => intro f s s' hg hv; cases f <;> simp [getAt?] at hg <;> simp only [replaceAt, tval, ih _ s s' hg hv]
  | right p ih => intro f s s' hg hv; cases f <;> simp [getAt?] at hg <;> simp only [replaceAt, tval, ih _ s s' hg hv]
  | body p ih => intro f s s' hg hv; cases f <;> simp [getAt?] at hg <;> simp only [replaceAt, tval, ih _ s s' hg hv]

/-- 🏁 Los 22 constructores de `Derives` conservan `tval`. Inducción sobre `Derives`: el núcleo la
    acepta, y cubre a todo habitante. -/
theorem derives_tval {Γ : List Formula} {f : Formula} (h : Γ ⊢ f) :
    ∀ a, allTrue a Γ → tval a f = true := by
  induction h with
  | hyp _ _ hf => exact fun a hΓ => hΓ _ hf
  | intro_impl _ A _ _ ih =>
      intro a hΓ; cases hA : tval a A
      · simp [tval, hA]
      · simp [tval, hA, ih a (allTrue_cons hA hΓ)]
  | elim_impl _ _ _ _ _ ih1 ih2 => intro a hΓ; have h1 := ih1 a hΓ; have h2 := ih2 a hΓ; simp_all [tval]
  | intro_and _ _ _ _ _ ih1 ih2 => intro a hΓ; simp [tval, ih1 a hΓ, ih2 a hΓ]
  | elim_and_l _ _ _ _ ih => intro a hΓ; have := ih a hΓ; simp_all [tval]
  | elim_and_r _ _ _ _ ih => intro a hΓ; have := ih a hΓ; simp_all [tval]
  | intro_or_l _ _ _ _ ih => intro a hΓ; simp [tval, ih a hΓ]
  | intro_or_r _ _ _ _ ih => intro a hΓ; simp [tval, ih a hΓ]
  | elim_or _ _ _ _ _ _ _ ih ih1 ih2 =>
      intro a hΓ; have h := ih a hΓ; simp only [tval, Bool.or_eq_true] at h
      rcases h with h | h
      · exact ih1 a (allTrue_cons h hΓ)
      · exact ih2 a (allTrue_cons h hΓ)
  | intro_forall _ _ _ ih => intro a hΓ; simpa [tval] using ih a (allTrue_lift hΓ)
  | elim_forall _ _ _ _ ih => intro a hΓ; rw [tval_subst]; simpa [tval] using ih a hΓ
  | intro_ex _ _ _ _ ih => intro a hΓ; have := ih a hΓ; rw [tval_subst] at this; simpa [tval] using this
  | elim_ex _ A _ _ _ ih1 ih2 =>
      intro a hΓ; have hA : tval a A = true := by simpa [tval] using ih1 a hΓ
      have := ih2 a (allTrue_cons hA (allTrue_lift hΓ)); rwa [tval_lift] at this
  | bot_elim _ _ _ ih => intro a hΓ; have := ih a hΓ; simp [tval] at this
  | weakening _ _ _ _ hs ih => intro a hΓ; exact ih a (allTrue_sub hs hΓ)
  | rewrite_at _ f _ p s s' _ hg hr he ih =>
      intro a hΓ; subst he; rw [tval_replaceAt a p f s s' hg (tval_localRule a hr)]; exact ih a hΓ
  | gen_rule _ _ _ ih => intro a hΓ; have := ih (.var 0) a hΓ; rw [tval_subst] at this; simpa [tval] using this
  | dne_rule _ A _ ih => intro a hΓ; have := ih a hΓ; cases hA : tval a A <;> simp_all [tval, neg]
  | dne_schema _ A => intro a _; cases hA : tval a A <;> simp [tval, neg, hA]
  | forall_not_ex_not _ A => intro a _; cases hA : tval a A <;> simp [tval, neg, hA]
  | refl _ _ => intro _ _; rfl
  | subst _ _ _ _ _ _ _ ih2 => intro a hΓ; have := ih2 a hΓ; rw [tval_subst] at this ⊢; exact this

/-- Un átomo no es derivable sin hipótesis: con la valuación `false`, `tval` lo hace falso. -/
theorem P_no : Not (([] : List Formula) ⊢ Formula.atom "P" []) := fun h => by
  have := derives_tval h false (fun _ hx => absurd hx List.not_mem_nil); simp [tval] at this

/-! ## §2 · Los ENUNCIADOS de los postulados, refutados SIN usarlos (valen para siempre) -/

/-- El enunciado de `FOL.MetaRules.imp_intro` (`MetaRules.lean:78`). -/
def ImpIntro : Prop := ∀ {Γ : List Formula} {A B : Formula}, (Γ ⊢ A → Γ ⊢ B) → Γ ⊢ (A ⇒ B)

/-- El enunciado de `FOL.MetaRules.raa` (`MetaRules.lean:110`). -/
def Raa : Prop := ∀ {Γ : List Formula} {A : Formula}, (Γ ⊢ A → Γ ⊢ Formula.bottom) → Γ ⊢ neg A

/-- El enunciado de `ROBINSON_PlusPlus.Full.ax_list_induction` (`Full/Lists.lean:79-82`). -/
def AxListInduction : Prop :=
  ∀ {Γ : List Formula} (φ : Term → Formula), (Γ ⊢ φ ROBINSON_PlusPlus.Minimal.Axioms.nil) →
    (∀ h t : Term, Γ ⊢ (φ t ⇒ φ (ROBINSON_PlusPlus.Minimal.Axioms.cons h t))) → ∀ L : Term, Γ ⊢ φ L

/-- 🏁 `imp_intro` es FALSO: su premisa, una función de Lean, se cumple VACUAMENTE para `P` no derivable. -/
theorem imp_intro_refutable : Not ImpIntro := fun H => by
  have := derives_tval (H (Γ := []) (A := Formula.atom "P" []) (B := Formula.bottom) (fun h => absurd h P_no))
    true (fun _ hx => absurd hx List.not_mem_nil)
  simp [tval] at this

/-- 🏁 `raa` es FALSO, por la misma razón. -/
theorem raa_refutable : Not Raa := fun H => by
  have := derives_tval (H (Γ := []) (A := Formula.atom "P" []) (fun h => absurd h P_no))
    true (fun _ hx => absurd hx List.not_mem_nil)
  simp [tval, neg] at this

/-- `φ` que mira la SINTAXIS del término: `⊥` en variables, `⊥ ⇒ ⊥` en aplicaciones. Como `nil` y
    `cons h t` son aplicaciones y la conclusión cuantifica sobre TODO término, sale `⊥`. -/
def phiBad : Term → Formula
  | .var _ => Formula.bottom
  | .func _ _ => Formula.impl Formula.bottom Formula.bottom

theorem top_der (Γ : List Formula) : Γ ⊢ Formula.impl Formula.bottom Formula.bottom :=
  Derives.intro_impl _ _ _ (Derives.hyp _ _ (List.Mem.head _))

/-- 🏁 `ax_list_induction` es FALSO: su `φ` no es uniforme y su `Γ` es libre. -/
theorem ax_list_induction_refutable : Not AxListInduction := fun H => by
  have hb : ([] : List Formula) ⊢ Formula.bottom :=
    H phiBad (top_der []) (fun _ t => Derives.intro_impl _ (phiBad t) _ (top_der _)) (.var 0)
  have := derives_tval hb true (fun _ hx => absurd hx List.not_mem_nil)
  simp [tval] at this

/-! ## §3 · Y por tanto el ENTORNO que los postula demuestra `False` (se borra al retirarlos) -/

theorem imp_intro_false : False := imp_intro_refutable (fun h => FOL.MetaRules.imp_intro h)
theorem raa_false : False := raa_refutable (fun h => FOL.MetaRules.raa h)
theorem ax_list_induction_false : False :=
  ax_list_induction_refutable (fun φ b s L => ROBINSON_PlusPlus.Full.ax_list_induction φ b s L)

end Sondeos.MetaReglasRefutables

#print axioms Sondeos.MetaReglasRefutables.derives_tval
#print axioms Sondeos.MetaReglasRefutables.imp_intro_refutable
#print axioms Sondeos.MetaReglasRefutables.raa_refutable
#print axioms Sondeos.MetaReglasRefutables.ax_list_induction_refutable
#print axioms Sondeos.MetaReglasRefutables.imp_intro_false
#print axioms Sondeos.MetaReglasRefutables.raa_false
#print axioms Sondeos.MetaReglasRefutables.ax_list_induction_false

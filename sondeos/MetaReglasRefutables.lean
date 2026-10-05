/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import FOL.FOL
import FOL.Finitary0
import FOL.Fresh0
import FOL.Soundness0
import FOL.Propositional0
import ROBINSON_PlusPlus.Minimal.Axioms

/-!
# SONDEO · L1‑3 — los postulados de la capa `⊢` son REFUTABLES (2026‑10‑02)

**Pregunta** (auditoría de la base, ronda 1: L1‑3, L2‑4 y L4‑1; ronda 2: R2‑4‑1): ¿es consistente el
entorno que RPP importaba, `FOL.FOL` + `FOL.MetaRules`? La doctrina escrita decía que sí mientras nadie
indujera sobre `Derives` (M‑11; `FOL/AXIOMS.md:293`, `FOL/FOL/Inconsistencia.lean:16-18` y `:66`,
ADR‑025: «RPP no está afectado»).

## 🏁 Respuesta, COMPILADA: no

1. `derives_tval` (§1): los 22 constructores de `Derives` son sólidos para la valuación booleana `tval`
   de `FOL.Finitary0`, por INDUCCIÓN y sin ningún axioma (`[propext, Quot.sound]`). El recursor cubre por
   definición a TODOS los habitantes, también a los que fabrican los `axiom`.
2. ⇒ los ENUNCIADOS de `imp_intro`, `raa` y `ax_list_induction` son FALSOS, y se demuestra sin usarlos
   (§2: `imp_intro_refutable`, `raa_refutable`, `ax_list_induction_refutable`).
3. ⇒ el entorno que los postulaba demostraba `False` (§3, hoy un REGISTRO: se borró al retirarlos).
4. Y los otros dos (§4, ronda 2): sin las meta‑reglas, `Derives` se traduce a `Derives₀`
   (`derives_to_derives0`) y es sólido para Tarski (`derives_soundness`) ⇒ `ex_elim` cae con un modelo
   de dos puntos y `or_elim` con el tercio excluso (`ex_elim_refutable`, `or_elim_refutable`).
   **Las cuatro meta‑reglas de `FOL/MetaRules.lean` son falsas**, no sólo dos.

🔑 *El problema nunca fue INDUCIR: el axioma es falso, y el recursor lo demuestra.* M‑11 evitaba ESCRIBIR la
contradicción, no la quitaba. Todo teorema con uno de estos axiomas en el footprint era teorema de una
teoría inconsistente: 53 de las 517 filas de `check-footprints.bash` el 2026‑10‑02 (42 de `ChainNegPrf`, con
`negVerifier_proved`; 5 de `CodeDistinct`; y `AxiomListCode`, `GodelTwo.d3`, `LineWFCases`, `OmegaStrength`
—`derives_completo`—, `VerifierSound` y una de FOL).

## Uso como control negativo

Decisión del propietario (2026‑10‑02): la capa `⊢` se retira como capa de trabajo y las meta‑reglas de FOL
se retiran, «no hacemos uso de herramientas que no sean verdaderas» (ADR‑115). Hecho: la §3 dejó de
compilar y se ha borrado (queda su registro). **La §2 y la §4 valen para siempre**: dicen que esos
enunciados no se pueden volver a postular sin hacer inconsistente a Lean.
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
theorem P_no : Not (([] : List Formula) ⊢ Formula.atom sym!"P" []) := fun h => by
  have := derives_tval h false (fun _ hx => absurd hx List.not_mem_nil); simp [tval] at this

/-! ## §2 · Los ENUNCIADOS de los postulados, refutados SIN usarlos (valen para siempre) -/

/-- El enunciado de `FOL.MetaRules.imp_intro` (`MetaRules.lean:78`; RPP dejó de importarlo con ADR‑115 y FOL lo
    retira). -/
def ImpIntro : Prop := ∀ {Γ : List Formula} {A B : Formula}, (Γ ⊢ A → Γ ⊢ B) → Γ ⊢ (A ⇒ B)

/-- El enunciado de `FOL.MetaRules.raa` (`MetaRules.lean:110`; RPP dejó de importarlo con ADR‑115 y FOL lo retira). -/
def Raa : Prop := ∀ {Γ : List Formula} {A : Formula}, (Γ ⊢ A → Γ ⊢ Formula.bottom) → Γ ⊢ neg A

/-- El enunciado de `ROBINSON_PlusPlus.Full.ax_list_induction` (`Full/Lists.lean:79-82`, retirado con
    ADR‑115). -/
def AxListInduction : Prop :=
  ∀ {Γ : List Formula} (φ : Term → Formula), (Γ ⊢ φ ROBINSON_PlusPlus.Minimal.Axioms.nil) →
    (∀ h t : Term, Γ ⊢ (φ t ⇒ φ (ROBINSON_PlusPlus.Minimal.Axioms.cons h t))) → ∀ L : Term, Γ ⊢ φ L

/-- 🏁 `imp_intro` es FALSO: su premisa, una función de Lean, se cumple VACUAMENTE para `P` no derivable. -/
theorem imp_intro_refutable : Not ImpIntro := fun H => by
  have := derives_tval (H (Γ := []) (A := Formula.atom sym!"P" []) (B := Formula.bottom) (fun h => absurd h P_no))
    true (fun _ hx => absurd hx List.not_mem_nil)
  simp [tval] at this

/-- 🏁 `raa` es FALSO, por la misma razón. -/
theorem raa_refutable : Not Raa := fun H => by
  have := derives_tval (H (Γ := []) (A := Formula.atom sym!"P" []) (fun h => absurd h P_no))
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

/-! ## §3 · REGISTRO — el ENTORNO que los postulaba demostraba `False` (borrado con ADR‑115)

Compilado el 2026‑10‑02 contra FOL `80d598c` y RPP `1dac85a`, antes de la retirada:

```lean
theorem imp_intro_false : False := imp_intro_refutable (fun h => FOL.MetaRules.imp_intro h)
theorem raa_false : False := raa_refutable (fun h => FOL.MetaRules.raa h)
theorem ax_list_induction_false : False :=
  ax_list_induction_refutable (fun φ b s L => ROBINSON_PlusPlus.Full.ax_list_induction φ b s L)
```

con footprints MEDIDOS `imp_intro_false` → `[propext, Quot.sound, FOL.MetaRules.imp_intro]` y
`raa_false` → `[propext, Quot.sound, FOL.MetaRules.raa]` (el de `ax_list_induction_false` quedó truncado en
la salida guardada: no se cita). Hoy no compilan: este fichero ya no importa `FOL.MetaRules` (que FOL
retira) y `ax_list_induction` ya no existe, que es exactamente lo que se buscaba.
-/

/-! ## §4 · Sin las meta‑reglas, `Derives` ES `Derives₀`, es sólido para Tarski, y las otras dos caen

Ronda 2 de la auditoría (R2‑4‑1). Esto es lo que respalda que retirar `FOL/MetaRules.lean` no pierde
NADA: lo que queda de `⊢` (los 22 constructores) se traduce al cálculo sólido y completo `⊢₀`. -/

section DerivesEsDerives0

open FOL.Eigenvariable FOL.Lift0 FOL.Fresh0 FOL.Metamath.Semantics
open FOL.Metamath.Soundness0 (Mtrue Mfalse P)

/-- El núcleo de `Henkin0.abs_neg_witness` (`:163`) sin el `neg`. -/
theorem abs_witness (c : List Char) (A : Formula) (hcA : Not (occursFormula c A)) :
    absFormula c 0 (substFormula 0 (Term.func c []) A) = A := by
  rw [absFormula_subst c A 0 0 (Nat.le_refl 0), absFormula_eq_lift c A 1 hcA]
  have hc : absTerm c 0 (Term.func c []) = Term.var 0 := by simp [absTerm]
  rw [hc, substFormula_lift_var A 0]

/-- 🏁 Los 22 constructores de `Derives` se traducen a `Derives₀`; `gen_rule` es ADMISIBLE: basta su
    premisa en UNA constante fresca. -/
theorem derives_to_derives0 {Γ : List Formula} {f : Formula} (h : Γ ⊢ f) : Γ ⊢₀ f := by
  induction h with
  | hyp Γ f hm => exact Derives₀.hyp Γ f hm
  | intro_impl Γ A B _ ih => exact Derives₀.intro_impl Γ A B ih
  | elim_impl Γ A B _ _ ih1 ih2 => exact Derives₀.elim_impl Γ A B ih1 ih2
  | intro_and Γ A B _ _ ih1 ih2 => exact Derives₀.intro_and Γ A B ih1 ih2
  | elim_and_l Γ A B _ ih => exact Derives₀.elim_and_l Γ A B ih
  | elim_and_r Γ A B _ ih => exact Derives₀.elim_and_r Γ A B ih
  | intro_or_l Γ A B _ ih => exact Derives₀.intro_or_l Γ A B ih
  | intro_or_r Γ A B _ ih => exact Derives₀.intro_or_r Γ A B ih
  | elim_or Γ A B C _ _ _ ih1 ih2 ih3 => exact Derives₀.elim_or Γ A B C ih1 ih2 ih3
  | intro_forall Γ A _ ih => exact Derives₀.intro_forall Γ A ih
  | elim_forall Γ A t _ ih => exact Derives₀.elim_forall Γ A t ih
  | intro_ex Γ A t _ ih => exact Derives₀.intro_ex Γ A t ih
  | elim_ex Γ A B _ _ ih1 ih2 => exact Derives₀.elim_ex Γ A B ih1 ih2
  | bot_elim Γ A _ ih => exact Derives₀.bot_elim Γ A ih
  | weakening Γ Γ' f _ hsub ih => exact Derives₀.weakening Γ Γ' f ih hsub
  | rewrite_at Γ f f' p sub sub' _ hget hrule heq ih =>
      exact Derives₀.rewrite_at Γ f f' p sub sub' ih hget hrule heq
  | gen_rule Γ A _ ih =>
      obtain ⟨N1, h1⟩ := cst_bound_list Γ
      obtain ⟨N2, h2⟩ := cst_bound_formula A
      have hΓ := h1 (max N1 N2) (Nat.le_max_left _ _)
      have hA := h2 (max N1 N2) (Nat.le_max_right _ _)
      have h := derives0_gen_fresh (cst (max N1 N2)) hΓ (ih (Term.func (cst (max N1 N2)) []))
      rwa [abs_witness _ A hA] at h
  | dne_rule Γ A _ ih => exact Derives₀.dne_rule Γ A ih
  | dne_schema Γ A => exact Derives₀.dne_schema Γ A
  | forall_not_ex_not Γ A => exact Derives₀.forall_not_ex_not Γ A
  | refl Γ t => exact Derives₀.refl Γ t
  | subst Γ t₁ t₂ f _ _ ih1 ih2 => exact Derives₀.subst Γ t₁ t₂ f ih1 ih2

/-- 🏁 La solidez de TARSKI de `Derives`: la que los docstrings de FOL llamaban FALSA. -/
theorem derives_soundness {Γ : List Formula} {f : Formula} (h : Γ ⊢ f) : satisfies Γ f :=
  derives0_soundness (derives_to_derives0 h)

private def MB : Model Bool := ⟨fun _ _ => false, fun _ ds => ds = [true]⟩
private def vB : Nat → Bool := fun _ => false
private def PA : Formula := Formula.atom sym!"P" [Term.var 0]

/-- 🏁 El ENUNCIADO de `FOL.MetaRules.ex_elim`, refutado sin usarlo (modelo de dos puntos). -/
theorem ex_elim_refutable :
    Not (∀ {Γ : List Formula} {A C : Formula}, (Γ ⊢ Formula.ex A) →
      (∀ t : Term, (Γ ⊢ substFormula 0 t A) → (Γ ⊢ C)) → (Γ ⊢ C)) := by
  intro hex
  have hΓ : contextSatisfies MB vB [Formula.ex PA] := by
    intro g hg
    cases hg with
    | head => simp [PA, MB, evalFormula, evalTerms, evalTerm, shiftEnv]
    | tail _ h => exact absurd h List.not_mem_nil
  have hterm : ∀ t : Term, evalTerm MB vB t = false := by
    intro t; cases t <;> simp [evalTerm, MB, vB]
  have hno : ∀ t : Term, Not ([Formula.ex PA] ⊢ substFormula 0 t PA) := by
    intro t ht
    have := derives_soundness ht Bool MB vB hΓ
    simp [PA, MB, substFormula, substTerms, substTerm, evalFormula, evalTerms] at this
    exact absurd this (by simpa [MB] using hterm t)
  exact derives_soundness
    (hex (Γ := [Formula.ex PA]) (A := PA) (C := Formula.bottom)
      (Derives.hyp _ _ (List.Mem.head _)) (fun t ht => absurd ht (hno t)))
    Bool MB vB hΓ

/-- 🏁 El ENUNCIADO de `FOL.MetaRules.or_elim`, refutado sin usarlo (tercio excluso y los dos modelos
    sobre `Unit`). -/
theorem or_elim_refutable :
    Not (∀ {Γ : List Formula} {A B C : Formula}, (Γ ⊢ Formula.or A B) →
      ((Γ ⊢ A) → (Γ ⊢ C)) → ((Γ ⊢ B) → (Γ ⊢ C)) → (Γ ⊢ C)) := by
  intro hor
  have hem : ([] : List Formula) ⊢ Formula.or P (neg P) :=
    derives0_to_derives (FOL.Propositional0.derives0_em_ctx [] P)
  have h1 : Not (([] : List Formula) ⊢ P) := fun h =>
    derives_soundness h Unit Mfalse (fun _ => ()) (fun _ hf => absurd hf List.not_mem_nil)
  have h2 : Not (([] : List Formula) ⊢ neg P) := fun h =>
    derives_soundness h Unit Mtrue (fun _ => ()) (fun _ hf => absurd hf List.not_mem_nil) trivial
  exact derives0_consistent (derives_to_derives0
    (hor (Γ := []) (A := P) (B := neg P) (C := Formula.bottom) hem
      (fun h => absurd h h1) (fun h => absurd h h2)))

end DerivesEsDerives0

end Sondeos.MetaReglasRefutables

#print axioms Sondeos.MetaReglasRefutables.derives_tval
#print axioms Sondeos.MetaReglasRefutables.imp_intro_refutable
#print axioms Sondeos.MetaReglasRefutables.raa_refutable
#print axioms Sondeos.MetaReglasRefutables.ax_list_induction_refutable
#print axioms Sondeos.MetaReglasRefutables.derives_to_derives0
#print axioms Sondeos.MetaReglasRefutables.derives_soundness
#print axioms Sondeos.MetaReglasRefutables.ex_elim_refutable
#print axioms Sondeos.MetaReglasRefutables.or_elim_refutable

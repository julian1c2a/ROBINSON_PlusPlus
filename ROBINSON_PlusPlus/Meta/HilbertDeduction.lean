/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.Hilbert

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Hilbert

namespace ROBINSON_PlusPlus.Meta.HilbertDeduction

/-!
## META — NIVEL D real: teorema de deducción finitario para `Prf`

Hacia `d2_prf` (y toda la cadena Gödel II en `Prf`) hace falta poder **descargar
hipótesis** (deducción) y **eliminar el ∃** dentro del cálculo finitario `Prf`. Como
`Prf` es Hilbert puro (sin contexto), introducimos un cálculo auxiliar **con
contexto** `PrfH Γ φ` (espejo de `Prf`: `incl0`/`p3`/`ind`/`qconf`/`mp` + `gen` de
**contexto-lift** como en `Derives.intro_forall`, más `hyp`), probamos el **teorema
de deducción** (el caso `gen` se cierra justo con el esquema de **confinamiento ∀**
`qconf`, ya integrado en el verificador), y el puente `PrfH [] φ ↔ Prf φ`.

Resultado clave: `prf_deduction : PrfH [A] B → Prf (A ⇒ B)` y
`prf_ex_elim_imp : PrfH [A] (↑C) → Prf (∃A ⇒ C)` (eliminación del ∃ vía `q3` + `gen`
+ deducción). `#print axioms` = solo `[propext, Classical.choice, Quot.sound]`
(ningún meta-axioma; `qconf` es un constructor de `Prf`, no un axioma Lean).
-/

/-- **Cálculo de Hilbert con contexto** (finitario), espejo de `Prf` más hipótesis.
    `gen` usa contexto-lift (eigenvariable seguro, como `Derives.intro_forall`). -/
inductive PrfH : List Formula → Formula → Prop where
  | hyp (Γ : List Formula) (φ : Formula) : List.Mem φ Γ → PrfH Γ φ
  | incl0 (Γ : List Formula) (φ : Formula) : Prf₀ φ → PrfH Γ φ
  | p3 (Γ : List Formula) (A : Formula) : PrfH Γ (((A ⇒ ⊥) ⇒ ⊥) ⇒ A)
  | ind (Γ : List Formula) (A : Formula) : PrfH Γ (Full.inductionFormula A)
  | qconf (Γ : List Formula) (P C : Formula) : PrfH Γ (confinementFormula P C)
  | listInd (Γ : List Formula) (A : Formula) : PrfH Γ (listInductionFormula A)
  | mp (Γ : List Formula) (A B : Formula) : PrfH Γ (A ⇒ B) → PrfH Γ A → PrfH Γ B
  | gen (Γ : List Formula) (A : Formula) :
      PrfH (Γ.map (liftFormula 0)) A → PrfH Γ (Formula.forall A)

/-- `A ⇒ A` intuicionista (de `p1`/`p2`/`mp`; combinador `I = S K K`). -/
theorem prf0_id (A : Formula) : Prf₀ (A ⇒ A) :=
  Prf₀.mp _ _ (Prf₀.mp _ _ (Prf₀.p2 A (A ⇒ A) A) (Prf₀.p1 A (A ⇒ A))) (Prf₀.p1 A A)

/-- Debilitamiento por la izquierda (combinador `K`): `PrfH Γ B → PrfH Γ (A ⇒ B)`. -/
theorem prfH_weaken {Γ : List Formula} {A B : Formula} (h : PrfH Γ B) : PrfH Γ (A ⇒ B) :=
  PrfH.mp Γ B (A ⇒ B) (PrfH.incl0 Γ (B ⇒ (A ⇒ B)) (Prf₀.p1 B A)) h

/-- Aplicación del combinador `S`: de `Γ ⊢ A⇒(C⇒B)` y `Γ ⊢ A⇒C` sale `Γ ⊢ A⇒B`. -/
theorem prfH_s_app {Γ : List Formula} {A C B : Formula}
    (h1 : PrfH Γ (A ⇒ (C ⇒ B))) (h2 : PrfH Γ (A ⇒ C)) : PrfH Γ (A ⇒ B) :=
  PrfH.mp Γ (A ⇒ C) (A ⇒ B)
    (PrfH.mp Γ (A ⇒ (C ⇒ B)) ((A ⇒ C) ⇒ (A ⇒ B)) (PrfH.incl0 Γ _ (Prf₀.p2 A C B)) h1) h2

/-- Hipótesis única: `PrfH [A] A`. -/
theorem prfH_hyp_self (A : Formula) : PrfH [A] A := PrfH.hyp [A] A (List.Mem.head _)

/-- **Teorema de deducción** (forma auxiliar, inducción sobre la derivación con la
    igualdad de contexto `Δ = A :: Γ`). El caso `gen` usa `qconf` (confinamiento ∀). -/
theorem deduction_aux {Δ B} (h : PrfH Δ B) : ∀ A Γ, Δ = A :: Γ → PrfH Γ (A ⇒ B) := by
  induction h with
  | hyp Δ' φ hmem =>
      intro A Γ hΔ; subst hΔ
      rcases List.mem_cons.mp hmem with rfl | hin
      · exact PrfH.incl0 Γ _ (prf0_id _)
      · exact prfH_weaken (PrfH.hyp Γ φ hin)
  | incl0 Δ' φ h0 => intro A Γ hΔ; subst hΔ; exact prfH_weaken (PrfH.incl0 Γ φ h0)
  | p3 Δ' A0 => intro A Γ hΔ; subst hΔ; exact prfH_weaken (PrfH.p3 Γ A0)
  | ind Δ' A0 => intro A Γ hΔ; subst hΔ; exact prfH_weaken (PrfH.ind Γ A0)
  | qconf Δ' P C => intro A Γ hΔ; subst hΔ; exact prfH_weaken (PrfH.qconf Γ P C)
  | listInd Δ' A0 => intro A Γ hΔ; subst hΔ; exact prfH_weaken (PrfH.listInd Γ A0)
  | mp Δ' C B' hCB hC ihCB ihC =>
      intro A Γ hΔ; subst hΔ
      exact prfH_s_app (ihCB A Γ rfl) (ihC A Γ rfl)
  | gen Δ' C hsub ih =>
      intro A Γ hΔ; subst hΔ
      have ihc : PrfH (Γ.map (liftFormula 0)) (liftFormula 0 A ⇒ C) :=
        ih (liftFormula 0 A) (Γ.map (liftFormula 0)) (by simp [List.map_cons])
      have hgen : PrfH Γ (Formula.forall (liftFormula 0 A ⇒ C)) := PrfH.gen Γ _ ihc
      have hq : PrfH Γ (confinementFormula A C) := PrfH.qconf Γ A C
      simp only [confinementFormula] at hq
      exact PrfH.mp Γ _ _ hq hgen

/-- Puente `PrfH [] φ → Prf φ` (sin hipótesis, `hyp` es imposible). -/
theorem prfH_nil_to_prf : ∀ {Γ φ}, PrfH Γ φ → Γ = [] → Prf φ := by
  intro Γ φ h
  induction h with
  | hyp Δ' ψ hmem => intro hΓ; subst hΓ; cases hmem
  | incl0 Δ' ψ h0 => intro _; exact Prf.incl h0
  | p3 Δ' A0 => intro _; exact Prf.p3 A0
  | ind Δ' A0 => intro _; exact Prf.ind A0
  | qconf Δ' P C => intro _; exact Prf.qconf P C
  | listInd Δ' A0 => intro _; exact Prf.listInd A0
  | mp Δ' A0 B0 hAB hA ihAB ihA => intro hΓ; subst hΓ; exact Prf.mp A0 B0 (ihAB rfl) (ihA rfl)
  | gen Δ' A0 hsub ih => intro hΓ; subst hΓ; exact Prf.gen A0 (ih (by simp))

/-- Puente `Prf φ → PrfH Γ φ` (todo teorema cerrado vive en cualquier contexto). -/
theorem prf_to_prfH {φ} (h : Prf φ) : ∀ Γ, PrfH Γ φ := by
  induction h with
  | incl h0 => intro Γ; exact PrfH.incl0 Γ _ h0
  | p3 A => intro Γ; exact PrfH.p3 Γ A
  | ind A => intro Γ; exact PrfH.ind Γ A
  | qconf P C => intro Γ; exact PrfH.qconf Γ P C
  | listInd A => intro Γ; exact PrfH.listInd Γ A
  | mp A B hAB hA ihAB ihA => intro Γ; exact PrfH.mp Γ A B (ihAB Γ) (ihA Γ)
  | gen A hA ih => intro Γ; exact PrfH.gen Γ A (ih (Γ.map (liftFormula 0)))

/-- **Teorema de deducción para `Prf`**: de `PrfH [A] B` sale `Prf (A ⇒ B)`. -/
theorem prf_deduction {A B : Formula} (h : PrfH [A] B) : Prf (A ⇒ B) :=
  prfH_nil_to_prf (deduction_aux h A [] rfl) rfl

/-- **Eliminación del ∃ como implicación**: de `PrfH [A] (↑C)` (probar `↑C` bajo la
    hipótesis `A` con la variable ligada libre) sale `Prf (∃A ⇒ C)` (vía `q3`+`gen`
    +deducción). Núcleo del `provCodeC'_elim` finitario para `d2_prf`. -/
theorem prf_ex_elim_imp {A C : Formula} (h : PrfH [A] (liftFormula 0 C)) :
    Prf (Formula.ex A ⇒ C) :=
  Prf.mp _ _ (Prf.incl (Prf₀.q3 A C)) (Prf.gen _ (prf_deduction h))

end ROBINSON_PlusPlus.Meta.HilbertDeduction

export ROBINSON_PlusPlus.Meta.HilbertDeduction (
  PrfH
  prfH_weaken
  prfH_s_app
  prfH_hyp_self
  prf_to_prfH
  prf_deduction
  prf_ex_elim_imp
)

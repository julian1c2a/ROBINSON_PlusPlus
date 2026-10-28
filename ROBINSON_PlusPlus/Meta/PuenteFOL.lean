/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.HilbertDeduction
import ROBINSON_PlusPlus.Meta.RigidezEstandar
import FOL.Derives1
import FOL.Canonical0

/-!
# `Meta/PuenteFOL.lean` — el puente de FOL a `Prf`, y Gödel I semántico (T67, ADR‑195)

Hasta aquí `goedel_I` decía que ESTE cálculo, `Prf` (un Hilbert propio), no deriva `G`, y nada unía `Prf` con la
consecuencia de primer orden de FOL (`AXIOMS.md` §0.1). Este módulo pone el puente en la dirección que hace falta:

* **§1 · `derives1_to_prfH`**: toda derivación de `Derives₁` (la deducción natural de FOL sin `rewrite_at`) es una de
  `PrfH`, con el MISMO contexto, constructor a constructor: la introducción de `⇒` es el teorema de deducción de
  `PrfH` (`deduction_aux`), la del `∀` es su `gen` (el contexto se levanta igual en los dos), la eliminación del `∃` es
  `q3` tras `gen`, y la igualdad es `leibniz`. El único caso con trabajo es `forall_not_ex_not` (`¬∀A ⇒ ∃¬A`), por
  reducción al absurdo dentro de `PrfH` (`forall_not_ex_not_prfH`). Con `derives0_to_derives1` de FOL, también para
  `Derives₀`.
* **§2 · `prf_of_derivesSet`**: si todo lo de `S` es teorema de `Prf`, todo lo que FOL deriva de `S` también
  (`DerivesSet₀`, la consecuencia sobre CONJUNTOS: un contexto finito dentro de `S`). Los teoremas de `Prf` son
  exactamente lo que FOL deriva de ellos (`prf_iff_derivesSet`).
* **§3 · `T_Prf` como teoría de primer orden**: `AxiomasT`, los 120 de `axioms` y las instancias de los dos esquemas
  de inducción (la lógica de `Prf` —`p3`, `qconf`, los esquemas de `Prfᵢ`— es de FOL). **`prf_completo`**: lo que vale
  en todo modelo de `AxiomasT`, `Prf` lo demuestra (por la existencia de modelo de FOL, `model_existence_lemma₀`).
* **§4 · Gödel I semántico**: `AxiomasT` no deriva ni `G` ni `¬G` en la lógica de primer orden de FOL
  (`goedel_I_fol`, `goedel_I_neg_fol`), ni `Con` (`goedel_II_fol`); y **`modelo_sin_G`**: hay un modelo de todos los
  teoremas de `Prf` en el que `G` es FALSA, mientras que `G` es verdadera en todo modelo estándar
  (`godelCN_verdadera_de`): ese modelo no es estándar (`goedel_I_semantico`).

⚠️ **Lo que NO dice.** La vuelta, `Prf → DerivesSet₀ AxiomasT`, no está: con instancias de los esquemas que tienen
variables libres, `gen` pide las clausuras universales, y para Gödel I no hace falta. La solidez de `Prf` sigue siendo
la de los modelos estándar (`prf_sound`, `prf_sound_dn`), no la de todo modelo de `AxiomasT` evaluado en una sola
valuación. Las §3 y §4 llevan `Classical.choice`: el de la completitud de FOL (`model_existence_lemma₀`, esencial,
`../FOL/AXIOMS.md` §4.2).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ROBINSON_PlusPlus.Meta.PuenteFOL

open ROBINSON_PlusPlus.Meta.Hilbert ROBINSON_PlusPlus.Meta.HilbertDeduction
open FOL.Metamath.Semantics FOL.Henkin0

/-! ## §1 · De `Derives₁` a `PrfH`, con el mismo contexto -/

/-- `¬∀A ⇒ ∃¬A` en `PrfH`, por reducción al absurdo: con `¬∃¬A` y `¬∀A` en el contexto, dentro del `∀` (el contexto
    levantado), `¬A` daría `∃¬A` (`q2` con la variable ligada, `substFormula_lift_var`), luego `A`, luego `∀A` (`gen`),
    contra `¬∀A`. -/
theorem forall_not_ex_not_prfH (A : Formula) :
    PrfH [] (neg (Formula.forall A) ⇒ Formula.ex (neg A)) := by
  -- el contexto de dentro del `∀`: `¬A`, `↑¬∃¬A` y `↑¬∀A`
  have hsl : substFormula 0 (Term.var 0) (liftFormula 1 (neg A)) = neg A :=
    FOL.Lift0.substFormula_lift_var (neg A) 0
  have hq2 := PrfH.incl0 [neg A, liftFormula 0 (neg (Formula.ex (neg A))), liftFormula 0 (neg (Formula.forall A))] _
    (Prfᵢ.q2 (liftFormula 1 (neg A)) (Term.var 0))
  rw [hsl] at hq2
  have hex : PrfH [neg A, liftFormula 0 (neg (Formula.ex (neg A))), liftFormula 0 (neg (Formula.forall A))]
      (liftFormula 0 (Formula.ex (neg A))) :=
    PrfH.mp _ _ _ hq2 (PrfH.hyp _ _ (List.Mem.head _))
  have hbot : PrfH [neg A, liftFormula 0 (neg (Formula.ex (neg A))), liftFormula 0 (neg (Formula.forall A))]
      Formula.bottom :=
    PrfH.mp _ (liftFormula 0 (Formula.ex (neg A))) Formula.bottom
      (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))) hex
  -- fuera de `¬A`: `¬¬A`, y por `p3`, `A`
  have hA : PrfH [liftFormula 0 (neg (Formula.ex (neg A))), liftFormula 0 (neg (Formula.forall A))] A :=
    PrfH.mp _ _ A (PrfH.p3 _ A) (deduction_aux hbot (neg A) _ rfl)
  -- `gen`: el contexto de `hA` es el levantado de `[¬∃¬A, ¬∀A]`
  have hall : PrfH [neg (Formula.ex (neg A)), neg (Formula.forall A)] (Formula.forall A) :=
    PrfH.gen _ A hA
  have hbot2 : PrfH [neg (Formula.ex (neg A)), neg (Formula.forall A)] Formula.bottom :=
    PrfH.mp _ (Formula.forall A) Formula.bottom (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))) hall
  have hN : PrfH [neg (Formula.forall A)] (Formula.ex (neg A)) :=
    PrfH.mp _ _ _ (PrfH.p3 _ (Formula.ex (neg A))) (deduction_aux hbot2 (neg (Formula.ex (neg A))) _ rfl)
  exact deduction_aux hN (neg (Formula.forall A)) [] rfl

/-- 🏁 **El puente**: toda derivación de `Derives₁` es una de `PrfH` con el mismo contexto. Constructor a
    constructor; `intro_impl` es `deduction_aux`, `intro_forall` es `PrfH.gen` (los dos levantan el contexto),
    `elim_ex` es `q3` tras `gen`, `subst` es `leibniz`, `dne_rule` y `dne_schema` son `p3`. -/
theorem derives1_to_prfH : ∀ {Γ : List Formula} {f : Formula}, Derives₁ Γ f → PrfH Γ f := by
  intro Γ f h
  induction h with
  | hyp Γ f hf => exact PrfH.hyp Γ f hf
  | intro_impl Γ A B _ ih => exact deduction_aux ih A Γ rfl
  | elim_impl Γ A B _ _ ih1 ih2 => exact PrfH.mp Γ A B ih1 ih2
  | intro_and Γ A B _ _ ih1 ih2 =>
      exact PrfH.mp Γ B _ (PrfH.mp Γ A _ (PrfH.incl0 Γ _ (Prfᵢ.c1 A B)) ih1) ih2
  | elim_and_l Γ A B _ ih => exact PrfH.mp Γ _ A (PrfH.incl0 Γ _ (Prfᵢ.c2 A B)) ih
  | elim_and_r Γ A B _ ih => exact PrfH.mp Γ _ B (PrfH.incl0 Γ _ (Prfᵢ.c3 A B)) ih
  | intro_or_l Γ A B _ ih => exact PrfH.mp Γ A _ (PrfH.incl0 Γ _ (Prfᵢ.j1 A B)) ih
  | intro_or_r Γ A B _ ih => exact PrfH.mp Γ B _ (PrfH.incl0 Γ _ (Prfᵢ.j2 A B)) ih
  | elim_or Γ A B C _ _ _ ih ihA ihB =>
      exact PrfH.mp Γ _ C
        (PrfH.mp Γ _ _ (PrfH.mp Γ _ _ (PrfH.incl0 Γ _ (Prfᵢ.j3 A B C)) ih) (deduction_aux ihA A Γ rfl))
        (deduction_aux ihB B Γ rfl)
  | intro_forall Γ A _ ih => exact PrfH.gen Γ A ih
  | elim_forall Γ A t _ ih => exact PrfH.mp Γ _ _ (PrfH.incl0 Γ _ (Prfᵢ.q1 A t)) ih
  | intro_ex Γ A t _ ih => exact PrfH.mp Γ _ _ (PrfH.incl0 Γ _ (Prfᵢ.q2 A t)) ih
  | elim_ex Γ A B _ _ ih1 ih2 =>
      have h2 : PrfH Γ (Formula.forall (A ⇒ liftFormula 0 B)) :=
        PrfH.gen Γ _ (deduction_aux ih2 A _ rfl)
      exact PrfH.mp Γ _ B (PrfH.mp Γ _ _ (PrfH.incl0 Γ _ (Prfᵢ.q3 A B)) h2) ih1
  | bot_elim Γ A _ ih => exact PrfH.mp Γ Formula.bottom A (PrfH.incl0 Γ _ (Prfᵢ.efq A)) ih
  | weakening Γ Γ' f _ hsub ih => exact PrfH_mono ih Γ' (fun x hx => hsub x hx)
  | dne_rule Γ A _ ih => exact PrfH.mp Γ _ A (PrfH.p3 Γ A) ih
  | dne_schema Γ A => exact PrfH.p3 Γ A
  | forall_not_ex_not Γ A => exact PrfH_mono (forall_not_ex_not_prfH A) Γ (fun _ hm => nomatch hm)
  | refl Γ t => exact PrfH.incl0 Γ _ (Prfᵢ.eqrefl t)
  | subst Γ t₁ t₂ f _ _ ih1 ih2 =>
      exact PrfH.mp Γ _ _ (PrfH.mp Γ _ _ (PrfH.incl0 Γ _ (Prfᵢ.leibniz f t₁ t₂)) ih1) ih2

/-- El puente para `Derives₀` (por `derives0_to_derives1`, que elimina `rewrite_at`). -/
theorem derives0_to_prfH {Γ : List Formula} {f : Formula} (h : Derives₀ Γ f) : PrfH Γ f :=
  derives1_to_prfH (FOL.Derives1.derives0_to_derives1 h)

/-- Lo que `Derives₀` deriva sin hipótesis, `Prf` lo demuestra. -/
theorem prf_of_derives0 {f : Formula} (h : Derives₀ [] f) : Prf f :=
  prfH_nil_to_prf (derives0_to_prfH h) rfl

/-! ## §2 · Sobre conjuntos: `Prf` es cerrado bajo la consecuencia de FOL -/

/-- Cortar las hipótesis de `PrfH` con teoremas de `Prf`: por el teorema de deducción, una a una. -/
theorem prfH_cut : ∀ (Γ : List Formula) {f : Formula}, PrfH Γ f → (∀ g, List.Mem g Γ → Prf g) → Prf f
  | [], _, h, _ => prfH_nil_to_prf h rfl
  | g :: Γ, f, h, hΓ =>
      Prf.mp g f (prfH_cut Γ (deduction_aux h g Γ rfl) (fun g' hg' => hΓ g' (List.Mem.tail _ hg')))
        (hΓ g (List.Mem.head _))

/-- 🏁 Si todo lo de `S` es teorema de `Prf`, todo lo que FOL deriva de `S` también. -/
theorem prf_of_derivesSet {S : Formula → Prop} (hS : ∀ g, S g → Prf g) {f : Formula}
    (h : DerivesSet₀ S f) : Prf f := by
  obtain ⟨Γ, hΓ, hD⟩ := h
  exact prfH_cut Γ (derives0_to_prfH hD) (fun g hg => hS g (hΓ g hg))

/-- Los teoremas de `Prf` son EXACTAMENTE lo que FOL deriva de ellos. -/
theorem prf_iff_derivesSet {f : Formula} : Iff (Prf f) (DerivesSet₀ (fun g => Prf g) f) :=
  ⟨fun h => FOL.Lindenbaum0.derivesSet0_hyp h, prf_of_derivesSet (fun _ h => h)⟩

/-! ## §3 · `T_Prf` como teoría de primer orden, y la completitud de `Prf` -/

/-- Los axiomas de `T_Prf` como CONJUNTO de fórmulas de FOL: los 120 de `axioms` y las instancias de los dos esquemas
    de inducción. La lógica de `Prf` (los esquemas de `Prfᵢ`, `p3`, `qconf`) no hace falta: es de FOL. -/
def AxiomasT (φ : Formula) : Prop :=
  Or (List.Mem φ ROBINSON_PlusPlus.Minimal.Axioms.axioms)
    (Or (∃ A, φ = ROBINSON_PlusPlus.Full.inductionFormula A) (∃ A, φ = listInductionFormula A))

theorem prf_of_axiomasT {φ : Formula} (h : AxiomasT φ) : Prf φ := by
  rcases h with h | ⟨A, rfl⟩ | ⟨A, rfl⟩
  · exact Prf.incl (Prfᵢ.thy φ h)
  · exact Prf.ind A
  · exact Prf.listInd A

/-- Lo que FOL deriva de `AxiomasT`, `Prf` lo demuestra. -/
theorem prf_of_derivesSet_axiomasT {f : Formula} (h : DerivesSet₀ AxiomasT f) : Prf f :=
  prf_of_derivesSet (fun _ => prf_of_axiomasT) h

/-- Si `S` no deriva `f`, `S` con `¬f` es consistente (deducción y `dne_rule` de FOL). -/
theorem consistente_de {S : Formula → Prop} {f : Formula} (h : ¬ DerivesSet₀ S f) :
    IsConsistent₀ (fun x => Or (S x) (x = neg f)) := by
  intro hbot
  obtain ⟨Γ, hΓ, hD⟩ := FOL.Lindenbaum0.derivesSet0_intro_impl hbot
  exact h ⟨Γ, hΓ, Derives₀.dne_rule Γ f hD⟩

/-- 🏁 **`Prf` es COMPLETO** para su teoría: lo que vale en todo modelo de `AxiomasT` (en la valuación en que vale
    `AxiomasT`), `Prf` lo demuestra. Por la existencia de modelo de FOL y el puente. -/
theorem prf_completo {f : Formula}
    (h : ∀ (D : Type) (M : Model D) (v : Nat → D), (∀ φ, AxiomasT φ → evalFormula M v φ) → evalFormula M v f) :
    Prf f := by
  refine Classical.byContradiction (fun hn => ?_)
  have hc : ¬ DerivesSet₀ AxiomasT f := fun hd => hn (prf_of_derivesSet_axiomasT hd)
  obtain ⟨D, M, v, hM⟩ := FOL.Canonical0.model_existence_lemma₀ (consistente_de hc)
  exact hM (neg f) (Or.inr rfl) (h D M v (fun φ hφ => hM φ (Or.inl hφ)))

/-! ## §4 · Gödel I en la lógica de primer orden, y el modelo en que `G` es falsa -/

/-- 🏁 **Gödel I en FOL**: los axiomas de `T_Prf` no derivan `G` en la lógica de primer orden de FOL. -/
theorem goedel_I_fol : ¬ DerivesSet₀ AxiomasT ROBINSON_PlusPlus.Meta.DiagonalNumeral.godelCN :=
  fun h => ROBINSON_PlusPlus.Meta.Consistencia.goedel_I (prf_of_derivesSet_axiomasT h)

/-- Y tampoco `¬G`: `AxiomasT` es INCOMPLETA en FOL. -/
theorem goedel_I_neg_fol : ¬ DerivesSet₀ AxiomasT (neg ROBINSON_PlusPlus.Meta.DiagonalNumeral.godelCN) :=
  fun h => ROBINSON_PlusPlus.Meta.SolidezVerificador.goedel_I_neg (prf_of_derivesSet_axiomasT h)

/-- **Gödel II en FOL**: `AxiomasT` no deriva su consistencia. -/
theorem goedel_II_fol : ¬ DerivesSet₀ AxiomasT ROBINSON_PlusPlus.Meta.GodelTwo.consistencyFormula' :=
  fun h => ROBINSON_PlusPlus.Meta.Consistencia.goedel_II (prf_of_derivesSet_axiomasT h)

/-- 🏁 **Un modelo de `T_Prf` en el que `G` es FALSA**: satisface todos los teoremas de `Prf` y no `G`. Por la
    existencia de modelo de FOL sobre los teoremas de `Prf` y `¬G`, consistentes por `goedel_I` y el puente. -/
theorem modelo_sin_G : ∃ (D : Type) (M : Model D) (v : Nat → D),
    And (∀ φ, Prf φ → evalFormula M v φ) (¬ evalFormula M v ROBINSON_PlusPlus.Meta.DiagonalNumeral.godelCN) := by
  have hc : ¬ DerivesSet₀ (fun g => Prf g) ROBINSON_PlusPlus.Meta.DiagonalNumeral.godelCN :=
    fun hd => ROBINSON_PlusPlus.Meta.Consistencia.goedel_I (prf_of_derivesSet (fun _ h => h) hd)
  obtain ⟨D, M, v, hM⟩ := FOL.Canonical0.model_existence_lemma₀ (consistente_de hc)
  exact ⟨D, M, v, fun φ hφ => hM φ (Or.inl hφ), hM (neg _) (Or.inr rfl)⟩

/-- 🏁 **GÖDEL I SEMÁNTICO**: `G` es verdadera en todo modelo estándar (`godelCN_verdadera_de`) y falsa en un modelo
    de `T_Prf` (`modelo_sin_G`), que por eso no es estándar. -/
theorem goedel_I_semantico :
    And (∀ (M : Model Nat), ROBINSON_PlusPlus.Meta.SolidezPrf.Estandar M →
          ∀ v, evalFormula M v ROBINSON_PlusPlus.Meta.DiagonalNumeral.godelCN)
      (∃ (D : Type) (M : Model D) (v : Nat → D),
          And (∀ φ, Prf φ → evalFormula M v φ) (¬ evalFormula M v ROBINSON_PlusPlus.Meta.DiagonalNumeral.godelCN)) :=
  ⟨fun _ hM v => ROBINSON_PlusPlus.Meta.RigidezEstandar.godelCN_verdadera_de hM v, modelo_sin_G⟩

end ROBINSON_PlusPlus.Meta.PuenteFOL

#print axioms ROBINSON_PlusPlus.Meta.PuenteFOL.derives1_to_prfH
#print axioms ROBINSON_PlusPlus.Meta.PuenteFOL.prf_of_derivesSet
#print axioms ROBINSON_PlusPlus.Meta.PuenteFOL.prf_completo
#print axioms ROBINSON_PlusPlus.Meta.PuenteFOL.goedel_I_fol
#print axioms ROBINSON_PlusPlus.Meta.PuenteFOL.goedel_I_neg_fol
#print axioms ROBINSON_PlusPlus.Meta.PuenteFOL.goedel_II_fol
#print axioms ROBINSON_PlusPlus.Meta.PuenteFOL.modelo_sin_G
#print axioms ROBINSON_PlusPlus.Meta.PuenteFOL.goedel_I_semantico

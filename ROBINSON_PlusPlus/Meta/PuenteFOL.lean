/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.HilbertDeduction
import ROBINSON_PlusPlus.Meta.RigidezEstandar
import FOL.Derives1
import FOL.Canonical0
import FOL.Sentence
import ROBINSON_PlusPlus.Meta.TarskiPrf

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
* **§3bis · Las clausuras universales de `AxiomasT`** (ADR‑253): `ClausurasT`, sentencias y teoremas de `Prf`; un
  modelo de ellas en una valuación satisface `AxiomasT` en TODAS (`axiomasT_global`); y la VUELTA del puente:
  `Prf f ↔ DerivesSet₀ ClausurasT f` (`prf_iff_derivesSet_clausuras`), sin `Classical.choice`: `T_Prf` es la teoría de
  primer orden, en el sentido de libro, de las clausuras de `AxiomasT`. Con ellas, `prf_completo` es la completitud de
  libro (hipótesis en toda valuación) y el modelo de `modelo_sin_G`, un modelo en el sentido usual.
* **§4 · Gödel I y II en FOL, y Gödel I semántico**: ningún conjunto de teoremas de `Prf` deriva en la lógica de
  primer orden de FOL ni `G` ni `¬G` (`goedel_I_fol`, `goedel_I_neg_fol`), ni `Con` (`goedel_II_fol`): ni `AxiomasT`,
  ni sus clausuras universales, ni todos los teoremas a la vez. Los tres son TITULARES (ADR‑210). Y
  **`modelo_sin_G`**: hay un modelo de todos los teoremas de `Prf` en el que `G` es FALSA, mientras que `G` es
  verdadera en todo modelo estándar (`godelCN_verdadera_de`); `goedel_I_semantico` junta los dos hechos, y de ahí se lee
  que ese modelo no es estándar (el teorema no lo enuncia: los modelos estándar son sobre ℕ). ✏️ 2026‑11‑02 (ADR‑250):
  `prf_completo`, `modelo_sin_G` y `goedel_I_semantico` también son TITULARES, con su `Classical.choice`.
* **§5 · Las sentencias, con FOL** (T72, ADR‑215): la `IsSentence` de RPP (`liftFormula 0 φ = φ`, `Meta/TarskiPrf.lean`)
  es la de FOL (`FOL.Sentence.IsSentence`: sin variables libres, decidible), `isSentence_iff_fol`; y `G` es una
  sentencia de FOL, así que su valor no depende de la valuación (`godelCN_eval_indep`): el de `modelo_sin_G`, tampoco.

⚠️ **Lo que NO dice.** La vuelta sobre `AxiomasT` mismo, `Prf → DerivesSet₀ AxiomasT`, no está: con instancias de
los esquemas que tienen variables libres, `gen` pide las clausuras universales. ✏️ 2026‑11‑03 (ADR‑253): sobre sus
CLAUSURAS sí, §3bis: `prf_iff_derivesSet_clausuras`, sin `Classical.choice`. La solidez de `Prf` sigue siendo
la de los modelos estándar (`prf_sound`, `prf_sound_dn`), no la de todo modelo de `AxiomasT` evaluado en una sola
valuación. En §3 y §4 llevan `Classical.choice` `prf_completo`, `modelo_sin_G` y `goedel_I_semantico` —no los tres
sintácticos—: el de la completitud de FOL (`model_existence_lemma₀`, esencial: `../FOL/AXIOMS.md` §4.3 y E7 de
`FOL.Esencialidad0`), y `prf_completo`, además, el de su propio `Classical.byContradiction`. ✏️ 2026‑10‑28 (R3‑4‑02 y
R3‑5‑03 de la ronda 3): decía que todo §3 y §4 lo llevaba, y citaba §4.2.
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

/-! ## §3bis · Las clausuras universales de `AxiomasT` (ADR‑253): de una valuación a todas, y la vuelta del puente

La semántica de FOL es de UNA valuación (`satisfies`, `model_existence_lemma₀`), y `AxiomasT` lleva las instancias de
los esquemas con parámetros libres. Aquí, las CLAUSURAS: `∀ⁿ φ`, con `φ` en `AxiomasT` y sus variables libres por
debajo de `n`. Son sentencias y teoremas de `Prf`. Un modelo de las clausuras en una valuación satisface `AxiomasT` en
TODAS (`axiomasT_global`), y `Prf` es exactamente lo que FOL deriva de ellas (`prf_iff_derivesSet_clausuras`): `T_Prf`
es la teoría de primer orden, en el sentido de libro, de las clausuras de `AxiomasT`. -/

section Clausuras

open ROBINSON_PlusPlus.Minimal.Axioms (forallN axioms)

mutual
/-- Una cota de las variables de un término: todas son menores que ella. -/
def cotaT : Term → Nat
  | .var k => k + 1
  | .func _ ts => cotaTs ts
def cotaTs : List Term → Nat
  | [] => 0
  | t :: ts => max (cotaT t) (cotaTs ts)
end

/-- Una cota de las variables LIBRES de una fórmula (bajo un binder, una menos). -/
def cotaF : Formula → Nat
  | .bottom => 0
  | .atom _ ts => cotaTs ts
  | .eq a b => max (cotaT a) (cotaT b)
  | .impl a b => max (cotaF a) (cotaF b)
  | .forall a => cotaF a - 1
  | .and a b => max (cotaF a) (cotaF b)
  | .or a b => max (cotaF a) (cotaF b)
  | .ex a => cotaF a - 1

mutual
theorem closedAtTerm_cota (t : Term) (n : Nat) (h : cotaT t ≤ n) :
    FOL.Sentence.closedAtTerm n t = true := by
  match t with
  | .var k =>
    unfold FOL.Sentence.closedAtTerm
    unfold cotaT at h
    exact decide_eq_true (by omega)
  | .func _ ts =>
    unfold FOL.Sentence.closedAtTerm
    unfold cotaT at h
    exact closedAtTerms_cota ts n h
theorem closedAtTerms_cota (ts : List Term) (n : Nat) (h : cotaTs ts ≤ n) :
    FOL.Sentence.closedAtTerms n ts = true := by
  match ts with
  | [] => rfl
  | t :: ts' =>
    unfold FOL.Sentence.closedAtTerms
    unfold cotaTs at h
    rw [Bool.and_eq_true]
    exact ⟨closedAtTerm_cota t n (by omega), closedAtTerms_cota ts' n (by omega)⟩
end

theorem closedAt_cota (φ : Formula) : ∀ n, cotaF φ ≤ n → FOL.Sentence.closedAt n φ = true := by
  induction φ with
  | bottom => intro _ _; rfl
  | atom _ ts => intro n h; exact closedAtTerms_cota ts n h
  | eq a b =>
    intro n h
    unfold cotaF at h
    show (FOL.Sentence.closedAtTerm n a && FOL.Sentence.closedAtTerm n b) = true
    rw [Bool.and_eq_true]
    exact ⟨closedAtTerm_cota a n (by omega), closedAtTerm_cota b n (by omega)⟩
  | impl a b iha ihb =>
    intro n h
    unfold cotaF at h
    show (FOL.Sentence.closedAt n a && FOL.Sentence.closedAt n b) = true
    rw [Bool.and_eq_true]
    exact ⟨iha n (by omega), ihb n (by omega)⟩
  | «forall» a ih =>
    intro n h
    unfold cotaF at h
    exact ih (n + 1) (by omega)
  | and a b iha ihb =>
    intro n h
    unfold cotaF at h
    show (FOL.Sentence.closedAt n a && FOL.Sentence.closedAt n b) = true
    rw [Bool.and_eq_true]
    exact ⟨iha n (by omega), ihb n (by omega)⟩
  | or a b iha ihb =>
    intro n h
    unfold cotaF at h
    show (FOL.Sentence.closedAt n a && FOL.Sentence.closedAt n b) = true
    rw [Bool.and_eq_true]
    exact ⟨iha n (by omega), ihb n (by omega)⟩
  | ex a ih =>
    intro n h
    unfold cotaF at h
    exact ih (n + 1) (by omega)

/-- Toda fórmula tiene sus variables libres por debajo de su cota. -/
theorem existe_cota (φ : Formula) : FOL.Sentence.closedAt (cotaF φ) φ = true :=
  closedAt_cota φ _ (Nat.le_refl _)

theorem closedAt_forallN : ∀ (k n : Nat) (φ : Formula),
    FOL.Sentence.closedAt n (forallN k φ) = FOL.Sentence.closedAt (n + k) φ
  | 0, _, _ => rfl
  | k + 1, n, φ => by
    show FOL.Sentence.closedAt (n + 1) (forallN k φ) = _
    rw [closedAt_forallN k (n + 1) φ]
    congr 1
    omega

theorem prf_forallN (φ : Formula) (h : Prf φ) : ∀ k, Prf (forallN k φ)
  | 0 => h
  | k + 1 => Prf.gen _ (prf_forallN φ h k)

/-- La clausura, evaluada: lo que vale `∀ᵏ φ` en `v`, `φ` lo vale en toda valuación que coincide con `v` desplazada
    `k` posiciones. -/
theorem eval_forallN {D : Type} (M : Model D) (φ : Formula) :
    ∀ (k : Nat) (v u : Nat → D), (∀ i, u (i + k) = v i) →
      evalFormula M v (forallN k φ) → evalFormula M u φ
  | 0, v, u, hu, h => by
    have e : u = v := funext fun i => hu i
    rw [e]
    exact h
  | k + 1, v, u, hu, h => by
    refine eval_forallN M φ k (shiftEnv v (u k)) u ?_ (h (u k))
    intro i
    cases i with
    | zero => show u (0 + k) = u k; rw [Nat.zero_add]
    | succ j =>
      show u (j + 1 + k) = v j
      rw [show j + 1 + k = j + (k + 1) by omega]
      exact hu j

/-- Si la clausura `∀ᵏ φ` vale en UNA valuación y las variables libres de `φ` están por debajo de `k`, `φ` vale en
    TODAS. -/
theorem eval_forallN_toda {D : Type} (M : Model D) {φ : Formula} {k : Nat}
    (hc : FOL.Sentence.closedAt k φ = true) {v : Nat → D} (h : evalFormula M v (forallN k φ)) (w : Nat → D) :
    evalFormula M w φ := by
  have hu : evalFormula M (fun i => if i < k then w i else v (i - k)) φ := by
    refine eval_forallN M φ k v _ (fun i => ?_) h
    have hi : ¬ (i + k < k) := by omega
    show (if i + k < k then w (i + k) else v (i + k - k)) = v i
    split
    · exact absurd ‹i + k < k› hi
    · rw [Nat.add_sub_cancel]
  refine (FOL.Sentence.evalFormula_agree M φ k _ w (fun i hi => ?_) hc).mp hu
  show (if i < k then w i else v (i - k)) = w i
  split
  · rfl
  · exact absurd hi ‹¬ i < k›

/-- Las CLAUSURAS universales de los axiomas de `T_Prf`: `∀ᵏ φ`, con `φ` en `AxiomasT` y sus variables libres por
    debajo de `k`. -/
def ClausurasT (σ : Formula) : Prop :=
  ∃ φ k, And (AxiomasT φ) (And (FOL.Sentence.closedAt k φ = true) (σ = forallN k φ))

/-- Las clausuras son SENTENCIAS. -/
theorem clausurasT_sentence {σ : Formula} (h : ClausurasT σ) : FOL.Sentence.IsSentence σ := by
  obtain ⟨φ, k, _, hc, rfl⟩ := h
  show FOL.Sentence.closedAt 0 (forallN k φ) = true
  rw [closedAt_forallN, Nat.zero_add]
  exact hc

/-- Las clausuras son TEOREMAS de `Prf` (por `gen`). -/
theorem prf_of_clausurasT {σ : Formula} (h : ClausurasT σ) : Prf σ := by
  obtain ⟨φ, k, hφ, _, rfl⟩ := h
  exact prf_forallN φ (prf_of_axiomasT hφ) k

theorem clausurasT_de {φ : Formula} (h : AxiomasT φ) : ClausurasT (forallN (cotaF φ) φ) :=
  ⟨φ, cotaF φ, h, existe_cota φ, rfl⟩

/-- 🏁 **De una valuación a todas**: un modelo de las clausuras de `AxiomasT`, en UNA valuación, satisface
    `AxiomasT` en TODAS. -/
theorem axiomasT_global {D : Type} {M : Model D} {v : Nat → D}
    (h : ∀ σ, ClausurasT σ → evalFormula M v σ) : ∀ φ, AxiomasT φ → ∀ w, evalFormula M w φ :=
  fun φ hφ w => eval_forallN_toda M (existe_cota φ) (h _ (clausurasT_de hφ)) w

/-! ### La vuelta del puente: lo que `Prf` demuestra, FOL lo deriva de las clausuras -/

/-- Un contexto de sentencias no cambia al levantarlo. -/
theorem map_lift_sentencias {Γ : List Formula} (hΓ : ∀ g, g ∈ Γ → FOL.Sentence.IsSentence g) :
    Γ.map (liftFormula 0) = Γ := by
  induction Γ with
  | nil => rfl
  | cons g Γ ih =>
    rw [List.map_cons, (FOL.Sentence.isSentence_iff_lift g).mp (hΓ g (List.Mem.head _)),
      ih (fun g' hg' => hΓ g' (List.Mem.tail _ hg'))]

/-- Con un contexto de sentencias, de `∀A` se sigue `A` (la variable ligada pasa a ser la 0). -/
theorem derives0_inst {Γ : List Formula} (hΓ : Γ.map (liftFormula 0) = Γ) {A : Formula}
    (h : Derives₀ Γ (Formula.forall A)) : Derives₀ Γ A := by
  have h1 : Derives₀ Γ (Formula.forall (liftFormula 1 A)) := by
    have h0 := FOL.Lift0.derives0_lift h 0
    rw [hΓ] at h0
    exact h0
  have h2 := Derives₀.elim_forall Γ (liftFormula 1 A) (Term.var 0) h1
  have e : substFormula 0 (Term.var 0) (liftFormula 1 A) = A := FOL.Lift0.substFormula_lift_var A 0
  rwa [e] at h2

theorem derives0_forallN {Γ : List Formula} (hΓ : Γ.map (liftFormula 0) = Γ) {φ : Formula} :
    ∀ k, Derives₀ Γ (forallN k φ) → Derives₀ Γ φ
  | 0, h => h
  | k + 1, h => derives0_forallN hΓ k (derives0_inst hΓ h)

/-- Un axioma de `AxiomasT`, derivado en FOL de su clausura. -/
theorem derivesSet_clausuras_axiomasT {φ : Formula} (h : AxiomasT φ) : DerivesSet₀ ClausurasT φ := by
  have hσ := clausurasT_de h
  have hΓ : [forallN (cotaF φ) φ].map (liftFormula 0) = [forallN (cotaF φ) φ] :=
    map_lift_sentencias (fun g hg => by cases hg with
      | head => exact clausurasT_sentence hσ
      | tail _ h' => nomatch h')
  refine ⟨[forallN (cotaF φ) φ], fun g hg => ?_, derives0_forallN hΓ _ (Derives₀.hyp _ _ (List.Mem.head _))⟩
  cases hg with
  | head => exact hσ
  | tail _ h' => nomatch h'

theorem derivesSet_vacio {S : Formula → Prop} {f : Formula} (h : Derives₀ [] f) : DerivesSet₀ S f :=
  ⟨[], ⟨(fun g (hg : g ∈ ([] : List Formula)) => nomatch hg), h⟩⟩

/-- `gen`, sobre las clausuras: el contexto son sentencias, y la regla del `∀` no lo cambia. -/
theorem derivesSet_clausuras_gen {A : Formula} (h : DerivesSet₀ ClausurasT A) :
    DerivesSet₀ ClausurasT (Formula.forall A) := by
  obtain ⟨Γ, hΓ, hD⟩ := h
  refine ⟨Γ, hΓ, Derives₀.intro_forall Γ A ?_⟩
  rw [map_lift_sentencias (fun g hg => clausurasT_sentence (hΓ g hg))]
  exact hD

theorem mem_lift_eq_self {l : List Formula} (h : l.map (liftFormula 0) = l) :
    ∀ a, a ∈ l → liftFormula 0 a = a := by
  induction l with
  | nil => intro a ha; nomatch ha
  | cons b l ih =>
    intro a ha
    rw [List.map_cons, List.cons.injEq] at h
    cases ha with
    | head => exact h.1
    | tail _ ha' => exact ih h.2 a ha'

/-- Los esquemas lógicos de `Prfᵢ`, derivados en FOL desde las clausuras. -/
theorem derivesSet_clausuras_of_prfI {f : Formula} (h : Prfᵢ f) : DerivesSet₀ ClausurasT f := by
  induction h with
  | p1 A B =>
    exact derivesSet_vacio (Derives₀.intro_impl _ _ _ (Derives₀.intro_impl _ _ _
      (Derives₀.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))))
  | p2 A B C =>
    refine derivesSet_vacio (Derives₀.intro_impl _ _ _ (Derives₀.intro_impl _ _ _ (Derives₀.intro_impl _ _ _ ?_)))
    have hA : Derives₀ [A, A ⇒ B, A ⇒ (B ⇒ C)] A := Derives₀.hyp _ _ (List.Mem.head _)
    have hAB : Derives₀ [A, A ⇒ B, A ⇒ (B ⇒ C)] (A ⇒ B) :=
      Derives₀.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
    have hABC : Derives₀ [A, A ⇒ B, A ⇒ (B ⇒ C)] (A ⇒ (B ⇒ C)) :=
      Derives₀.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    exact Derives₀.elim_impl _ _ _ (Derives₀.elim_impl _ _ _ hABC hA) (Derives₀.elim_impl _ _ _ hAB hA)
  | c1 A B =>
    exact derivesSet_vacio (Derives₀.intro_impl _ _ _ (Derives₀.intro_impl _ _ _ (Derives₀.intro_and _ _ _
      (Derives₀.hyp _ _ (List.Mem.tail _ (List.Mem.head _))) (Derives₀.hyp _ _ (List.Mem.head _)))))
  | c2 A B =>
    exact derivesSet_vacio (Derives₀.intro_impl _ _ _
      (Derives₀.elim_and_l _ A B (Derives₀.hyp _ _ (List.Mem.head _))))
  | c3 A B =>
    exact derivesSet_vacio (Derives₀.intro_impl _ _ _
      (Derives₀.elim_and_r _ A B (Derives₀.hyp _ _ (List.Mem.head _))))
  | j1 A B =>
    exact derivesSet_vacio (Derives₀.intro_impl _ _ _ (Derives₀.intro_or_l _ _ _ (Derives₀.hyp _ _ (List.Mem.head _))))
  | j2 A B =>
    exact derivesSet_vacio (Derives₀.intro_impl _ _ _ (Derives₀.intro_or_r _ _ _ (Derives₀.hyp _ _ (List.Mem.head _))))
  | j3 A B C =>
    refine derivesSet_vacio (Derives₀.intro_impl _ _ _ (Derives₀.intro_impl _ _ _ (Derives₀.intro_impl _ _ _ ?_)))
    refine Derives₀.elim_or _ A B C
      (Derives₀.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) ?_ ?_
    · exact Derives₀.elim_impl _ A C (Derives₀.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
        (Derives₀.hyp _ _ (List.Mem.head _))
    · exact Derives₀.elim_impl _ B C (Derives₀.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))
        (Derives₀.hyp _ _ (List.Mem.head _))
  | efq A =>
    exact derivesSet_vacio (Derives₀.intro_impl _ _ _ (Derives₀.bot_elim _ _ (Derives₀.hyp _ _ (List.Mem.head _))))
  | q1 A t =>
    exact derivesSet_vacio (Derives₀.intro_impl _ _ _
      (Derives₀.elim_forall _ A t (Derives₀.hyp _ _ (List.Mem.head _))))
  | q2 A t =>
    exact derivesSet_vacio (Derives₀.intro_impl _ _ _
      (Derives₀.intro_ex _ A t (Derives₀.hyp _ _ (List.Mem.head _))))
  | q3 A B =>
    refine derivesSet_vacio (Derives₀.intro_impl _ _ _ (Derives₀.intro_impl _ _ _ ?_))
    refine Derives₀.elim_ex _ A B (Derives₀.hyp _ _ (List.Mem.head _)) ?_
    -- en el contexto levantado, `↑∀(A ⇒ ↑B) = ∀(↑₁A ⇒ ↑₁↑B)`; con la variable 0, `A ⇒ ↑B`
    have hF : Derives₀ (A :: List.map (liftFormula 0) [Formula.ex A, Formula.forall (A ⇒ liftFormula 0 B)])
        (Formula.forall (liftFormula 1 A ⇒ liftFormula 1 (liftFormula 0 B))) :=
      Derives₀.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    have hI : Derives₀ (A :: List.map (liftFormula 0) [Formula.ex A, Formula.forall (A ⇒ liftFormula 0 B)])
        (substFormula 0 (Term.var 0) (liftFormula 1 A) ⇒
          substFormula 0 (Term.var 0) (liftFormula 1 (liftFormula 0 B))) :=
      Derives₀.elim_forall _ _ (Term.var 0) hF
    have e1 : substFormula 0 (Term.var 0) (liftFormula 1 A) = A := FOL.Lift0.substFormula_lift_var A 0
    have e2 : substFormula 0 (Term.var 0) (liftFormula 1 (liftFormula 0 B)) = liftFormula 0 B :=
      FOL.Lift0.substFormula_lift_var (liftFormula 0 B) 0
    rw [e1, e2] at hI
    exact Derives₀.elim_impl _ _ _ hI (Derives₀.hyp _ _ (List.Mem.head _))
  | eqrefl t => exact derivesSet_vacio (Derives₀.refl _ t)
  | leibniz A t₁ t₂ =>
    exact derivesSet_vacio (Derives₀.intro_impl _ _ _ (Derives₀.intro_impl _ _ _
      (Derives₀.subst _ t₁ t₂ A (Derives₀.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))
        (Derives₀.hyp _ _ (List.Mem.head _)))))
  | thy a ha =>
    have hl : liftFormula 0 a = a := mem_lift_eq_self axioms_lift_eq a ha
    refine FOL.Lindenbaum0.derivesSet0_hyp ⟨a, 0, Or.inl ha, ?_, rfl⟩
    exact (FOL.Sentence.isSentence_iff_lift a).mpr hl
  | mp A B _ _ ihAB ihA => exact FOL.Lindenbaum0.derivesSet0_elim_impl ihAB ihA
  | gen A _ ih => exact derivesSet_clausuras_gen ih

/-- 🏁 **La vuelta del puente**: lo que `Prf` demuestra, FOL lo deriva de las clausuras de `AxiomasT`. -/
theorem derivesSet_clausuras_of_prf {f : Formula} (h : Prf f) : DerivesSet₀ ClausurasT f := by
  induction h with
  | incl h0 => exact derivesSet_clausuras_of_prfI h0
  | p3 A => exact derivesSet_vacio (Derives₀.dne_schema [] A)
  | ind A => exact derivesSet_clausuras_axiomasT (Or.inr (Or.inl ⟨A, rfl⟩))
  | qconf P C =>
    refine derivesSet_vacio (Derives₀.intro_impl _ _ _ (Derives₀.intro_impl _ _ _ (Derives₀.intro_forall _ _ ?_)))
    -- el contexto levantado: `↑P` y `↑∀(↑P ⇒ C) = ∀(↑₁↑P ⇒ ↑₁C)`; con la variable 0, `↑P ⇒ C`
    have hF : Derives₀ (List.map (liftFormula 0) [P, Formula.forall (liftFormula 0 P ⇒ C)])
        (Formula.forall (liftFormula 1 (liftFormula 0 P) ⇒ liftFormula 1 C)) :=
      Derives₀.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
    have hI : Derives₀ (List.map (liftFormula 0) [P, Formula.forall (liftFormula 0 P ⇒ C)])
        (substFormula 0 (Term.var 0) (liftFormula 1 (liftFormula 0 P)) ⇒
          substFormula 0 (Term.var 0) (liftFormula 1 C)) :=
      Derives₀.elim_forall _ _ (Term.var 0) hF
    have e1 : substFormula 0 (Term.var 0) (liftFormula 1 (liftFormula 0 P)) = liftFormula 0 P :=
      FOL.Lift0.substFormula_lift_var (liftFormula 0 P) 0
    have e2 : substFormula 0 (Term.var 0) (liftFormula 1 C) = C := FOL.Lift0.substFormula_lift_var C 0
    rw [e1, e2] at hI
    exact Derives₀.elim_impl _ _ _ hI (Derives₀.hyp _ _ (List.Mem.head _))
  | listInd A => exact derivesSet_clausuras_axiomasT (Or.inr (Or.inr ⟨A, rfl⟩))
  | mp A B _ _ ihAB ihA => exact FOL.Lindenbaum0.derivesSet0_elim_impl ihAB ihA
  | gen A _ ih => exact derivesSet_clausuras_gen ih

/-- 🏁 **`T_Prf` ES la teoría de primer orden de las clausuras de `AxiomasT`**: `Prf` demuestra exactamente lo que FOL
    deriva de ellas. -/
theorem prf_iff_derivesSet_clausuras {f : Formula} : Iff (Prf f) (DerivesSet₀ ClausurasT f) :=
  ⟨derivesSet_clausuras_of_prf, prf_of_derivesSet (fun _ => prf_of_clausurasT)⟩

end Clausuras

/-- 🏁 **`Prf` es COMPLETO** para su teoría, en el sentido de libro: lo que vale en todo modelo de `AxiomasT` —en
    TODA valuación—, `Prf` lo demuestra. Por la existencia de modelo de FOL sobre las clausuras de `AxiomasT` y
    `axiomasT_global`. ✏️ 2026‑11‑03 (ADR‑253): la hipótesis era la de UNA valuación (la semántica de FOL), más fuerte;
    ésta es más débil y da un teorema más fuerte, del que aquél es un corolario (el `example` de abajo). Titular desde
    ADR‑250, con el `Classical.choice` de la completitud de FOL. -/
theorem prf_completo {f : Formula}
    (h : ∀ (D : Type) (M : Model D), (∀ φ, AxiomasT φ → ∀ w, evalFormula M w φ) → ∀ w, evalFormula M w f) :
    Prf f := by
  refine Classical.byContradiction (fun hn => ?_)
  have hc : ¬ DerivesSet₀ ClausurasT f := fun hd => hn (prf_iff_derivesSet_clausuras.mpr hd)
  obtain ⟨D, M, v, hM⟩ := FOL.Canonical0.model_existence_lemma₀ (consistente_de hc)
  exact hM (neg f) (Or.inr rfl) (h D M (axiomasT_global (fun σ hσ => hM σ (Or.inl hσ))) v)

-- La forma de una sola valuación, la de antes de ADR‑253, es un corolario.
example {f : Formula}
    (h : ∀ (D : Type) (M : Model D) (v : Nat → D), (∀ φ, AxiomasT φ → evalFormula M v φ) → evalFormula M v f) :
    Prf f :=
  prf_completo (fun D M hM w => h D M w (fun φ hφ => hM φ hφ w))

/-! ## §4 · Gödel I en la lógica de primer orden, y el modelo en que `G` es falsa -/

/-- 🏁 **Gödel I en FOL** (titular, ADR‑210): ningún conjunto `S` de teoremas de `Prf` deriva `G` en la lógica de
    primer orden de FOL. `S` puede ser `AxiomasT` (los 120 y las instancias de los dos esquemas: `prf_of_axiomasT`),
    sus clausuras universales (teoremas de `Prf` por `gen`) o todos los teoremas a la vez; el enunciado de libro, «las
    clausuras de T no derivan G», es una instancia, y no pide que los 120 sean sentencias. -/
theorem goedel_I_fol {S : Formula → Prop} (hS : ∀ φ, S φ → Prf φ) :
    ¬ DerivesSet₀ S ROBINSON_PlusPlus.Meta.DiagonalNumeral.godelCN :=
  fun h => ROBINSON_PlusPlus.Meta.Consistencia.goedel_I (prf_of_derivesSet hS h)

/-- 🏁 Y tampoco `¬G` (titular, ADR‑210): con `goedel_I_fol`, todo conjunto de teoremas de `Prf` es INCOMPLETO en
    FOL. -/
theorem goedel_I_neg_fol {S : Formula → Prop} (hS : ∀ φ, S φ → Prf φ) :
    ¬ DerivesSet₀ S (neg ROBINSON_PlusPlus.Meta.DiagonalNumeral.godelCN) :=
  fun h => ROBINSON_PlusPlus.Meta.SolidezVerificador.goedel_I_neg (prf_of_derivesSet hS h)

/-- 🏁 **Gödel II en FOL** (titular, ADR‑210): ningún conjunto de teoremas de `Prf` deriva en FOL la consistencia
    de `T_Prf`. -/
theorem goedel_II_fol {S : Formula → Prop} (hS : ∀ φ, S φ → Prf φ) :
    ¬ DerivesSet₀ S ROBINSON_PlusPlus.Meta.GodelTwo.consistencyFormula' :=
  fun h => ROBINSON_PlusPlus.Meta.Consistencia.goedel_II (prf_of_derivesSet hS h)

-- La hipótesis no es vacía: la cumplen `AxiomasT` y el conjunto de TODOS los teoremas de `Prf` (que contiene las
-- clausuras universales de los axiomas, por `gen`).
example : ¬ DerivesSet₀ AxiomasT ROBINSON_PlusPlus.Meta.DiagonalNumeral.godelCN :=
  goedel_I_fol (fun _ => prf_of_axiomasT)
example (A : Formula) (h : AxiomasT A) : Prf (Formula.forall A) := Prf.gen A (prf_of_axiomasT h)
example : ¬ DerivesSet₀ (fun g => Prf g) ROBINSON_PlusPlus.Meta.GodelTwo.consistencyFormula' :=
  goedel_II_fol (fun _ h => h)

-- Las clausuras de `AxiomasT` no derivan `G` en FOL: el enunciado de libro, una instancia más de `goedel_I_fol`.
example : ¬ DerivesSet₀ ClausurasT ROBINSON_PlusPlus.Meta.DiagonalNumeral.godelCN :=
  goedel_I_fol (fun _ => prf_of_clausurasT)

/-- 🏁 **Un modelo de `T_Prf` en el que `G` es FALSA**: satisface todos los teoremas de `Prf` en TODA valuación, y `G`
    en ninguna. Por la existencia de modelo de FOL sobre los teoremas de `Prf` y `¬G`, consistentes por `goedel_I` y el
    puente; de su valuación a todas, por las clausuras (`eval_forallN_toda`), y `G`, que es una sentencia, no depende
    de ella. ✏️ 2026‑11‑03 (ADR‑253): decía «en una valuación». Titular desde ADR‑250. -/
theorem modelo_sin_G : ∃ (D : Type) (M : Model D),
    And (∀ φ, Prf φ → ∀ w, evalFormula M w φ)
      (∀ w, ¬ evalFormula M w ROBINSON_PlusPlus.Meta.DiagonalNumeral.godelCN) := by
  have hc : ¬ DerivesSet₀ (fun g => Prf g) ROBINSON_PlusPlus.Meta.DiagonalNumeral.godelCN :=
    goedel_I_fol (fun _ h => h)
  obtain ⟨D, M, v, hM⟩ := FOL.Canonical0.model_existence_lemma₀ (consistente_de hc)
  refine ⟨D, M, fun φ hφ w => ?_, fun w hw => ?_⟩
  · exact eval_forallN_toda M (existe_cota φ) (hM _ (Or.inl (prf_forallN φ hφ _))) w
  · have hs : FOL.Sentence.IsSentence ROBINSON_PlusPlus.Meta.DiagonalNumeral.godelCN :=
      (FOL.Sentence.isSentence_iff_lift _).mpr ROBINSON_PlusPlus.Meta.TarskiPrf.godelCN_isSentence
    exact hM (neg _) (Or.inr rfl) ((FOL.Sentence.eval_sentence M hs w v).mp hw)

/-- 🏁 **GÖDEL I SEMÁNTICO**: `G` es verdadera en todo modelo estándar (`godelCN_verdadera_de`) y falsa, en TODA
    valuación, en un modelo de `T_Prf` (`modelo_sin_G`). Junta los dos hechos; que ese modelo no sea estándar es su
    lectura, no parte del enunciado (los modelos estándar son sobre ℕ). ✏️ 2026‑11‑03 (ADR‑253): el modelo, en toda
    valuación. Titular desde ADR‑250. -/
theorem goedel_I_semantico :
    And (∀ (M : Model Nat), ROBINSON_PlusPlus.Meta.SolidezPrf.Estandar M →
          ∀ v, evalFormula M v ROBINSON_PlusPlus.Meta.DiagonalNumeral.godelCN)
      (∃ (D : Type) (M : Model D),
          And (∀ φ, Prf φ → ∀ w, evalFormula M w φ)
            (∀ w, ¬ evalFormula M w ROBINSON_PlusPlus.Meta.DiagonalNumeral.godelCN)) :=
  ⟨fun _ hM v => ROBINSON_PlusPlus.Meta.RigidezEstandar.godelCN_verdadera_de hM v, modelo_sin_G⟩

/-! ## §5 · Las sentencias, con FOL (T72, ADR‑215) -/

/-- 🏁 La `IsSentence` de RPP (`liftFormula 0 φ = φ`) es la de FOL (sin variables libres, `FOL.Sentence`). -/
theorem isSentence_iff_fol (φ : Formula) :
    Iff (ROBINSON_PlusPlus.Meta.TarskiPrf.IsSentence φ) (FOL.Sentence.IsSentence φ) :=
  (FOL.Sentence.isSentence_iff_lift φ).symm

/-- `G` es una sentencia de FOL. -/
theorem godelCN_isSentence_fol : FOL.Sentence.IsSentence ROBINSON_PlusPlus.Meta.DiagonalNumeral.godelCN :=
  (isSentence_iff_fol _).mp ROBINSON_PlusPlus.Meta.TarskiPrf.godelCN_isSentence

/-- El valor de `G` en un modelo no depende de la valuación: el modelo de `modelo_sin_G` la hace falsa en TODAS. -/
theorem godelCN_eval_indep {D : Type} (M : Model D) (v w : Nat → D) :
    Iff (evalFormula M v ROBINSON_PlusPlus.Meta.DiagonalNumeral.godelCN)
      (evalFormula M w ROBINSON_PlusPlus.Meta.DiagonalNumeral.godelCN) :=
  FOL.Sentence.eval_sentence M godelCN_isSentence_fol v w

end ROBINSON_PlusPlus.Meta.PuenteFOL

#print axioms ROBINSON_PlusPlus.Meta.PuenteFOL.derives1_to_prfH
#print axioms ROBINSON_PlusPlus.Meta.PuenteFOL.prf_of_derivesSet
#print axioms ROBINSON_PlusPlus.Meta.PuenteFOL.axiomasT_global
#print axioms ROBINSON_PlusPlus.Meta.PuenteFOL.prf_iff_derivesSet_clausuras
#print axioms ROBINSON_PlusPlus.Meta.PuenteFOL.prf_completo
#print axioms ROBINSON_PlusPlus.Meta.PuenteFOL.goedel_I_fol
#print axioms ROBINSON_PlusPlus.Meta.PuenteFOL.goedel_I_neg_fol
#print axioms ROBINSON_PlusPlus.Meta.PuenteFOL.goedel_II_fol
#print axioms ROBINSON_PlusPlus.Meta.PuenteFOL.modelo_sin_G
#print axioms ROBINSON_PlusPlus.Meta.PuenteFOL.goedel_I_semantico
#print axioms ROBINSON_PlusPlus.Meta.PuenteFOL.isSentence_iff_fol
#print axioms ROBINSON_PlusPlus.Meta.PuenteFOL.godelCN_isSentence_fol
#print axioms ROBINSON_PlusPlus.Meta.PuenteFOL.godelCN_eval_indep

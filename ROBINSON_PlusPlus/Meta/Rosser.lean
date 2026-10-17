/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.RosserNegNum
import ROBINSON_PlusPlus.Meta.TarskiPrf

/-!
# `Meta/Rosser.lean` — 🏁 ROSSER, para toda extensión finita T+E, por REDUCCIÓN a T (ADR‑144, ADR‑145, ADR‑157)

**Qué.** `rosser_ext E hE hcon : ¬ PrfH E (R E) ∧ ¬ PrfH E ¬(R E)`: si T+E es consistente, su sentencia de Rosser es
indecidible en T+E. Y el corolario para la propia T, sin hipótesis: `rosser : ¬ Prf R ∧ ¬ Prf ¬R`, con `consistencia`.

* **§1** El cálculo de T+E es `PrfH E`, y por deducción `PrfH E φ ↔ Prf (impChain E φ)` (promovido de
  `sondeos/ExtensionPorReduccion.lean`, ADR‑144 §3).
* **§2** El código de `impChain E φ` es el de φ con un término delante (`formCode_impChain`), y el predicado de prueba
  de T+E se DEFINE con el de T: `PfE E y x := PfF y (impChainC E x)`. PosNum y NegNum de T+E (`posNumE`, `negNumE`)
  son los de T (ADR‑149, ADR‑156) sobre `impChain E φ`: no se calcula nada.
* **§3** La sentencia de Rosser, `R E`, es el punto fijo (`prf_diagonal`) de
  ρ_E(x) := ∀y (Pf_E(y, x) → ∃z (z < y ∧ Pf_E(z, ¬x))). Es una sentencia (`R_isSentence`). ADR‑144 escribía `z ≤ y`;
  con `z < y`, la forma de Rosser, basta la tricotomía de `<`.
* **§4** El argumento, con T+E consistente:
  - (a) una prueba m̄ de R da, por ρ, una de ¬R por debajo de m̄; T+E no prueba ¬R, así que NegNum las refuta todas
    (`prfH_bot_of`);
  - (b) una prueba m̄ de ¬R hace demostrable en T la propia ρ(⌜R⌝): por debajo de m̄ y en m̄, NegNum refuta las pruebas
    de R; por encima, m̄ es el testigo (`prf_rhoBody_of`). Así T prueba R, y T+E sería inconsistente.
* **§5** Los titulares: `rosser_red` (toda lista E), `rosser_ext` (el enunciado de ADR‑145) y `rosser` (E = []).
* **§6** Los controles: la hipótesis puede fallar (E = [⊥]) y entonces la conclusión falla; y las dos de `rosser_ext`
  pueden valer a la vez en una extensión NO sólida, T+¬Con (¬Con es una sentencia: `negCon_isSentence`), donde la
  solidez no puede sustituir a la consistencia.

⚠️ **`hE` no la usa la prueba** (ADR‑157 §2): la reducción vale para toda lista E, y `rosser_red` lo dice. Lo que hace
de `PrfH E` la teoría T+E es que E sean sentencias (ADR‑144 §7); por eso está en el enunciado de `rosser_ext`, con el
nombre `_hE`.

⛔ Ningún numeral se evalúa: el código ⌜R⌝ = `numeral (codeNat (R E))` sólo se mueve por `rw` con lemas ∀ (ADR‑117 §3).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open FOL ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.HilbertDeduction ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.DiagonalNumeral ROBINSON_PlusPlus.Meta.TarskiPrf
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs
open ROBINSON_PlusPlus.Meta.RosserPosNum ROBINSON_PlusPlus.Meta.RosserNegNum

namespace ROBINSON_PlusPlus.Meta.Rosser

/-! ## §1 · El cálculo de T+E, por deducción (de `sondeos/ExtensionPorReduccion.lean`) -/

/-- E en implicaciones delante de φ, en el orden en que el teorema de deducción las descarga: la cabeza de E queda
    más ADENTRO. `impChain [e₁, e₂] φ = e₂ ⇒ (e₁ ⇒ φ)`. -/
def impChain : List Formula → Formula → Formula
  | [], φ => φ
  | e :: E, φ => impChain E (e ⇒ φ)

/-- De T+E a T: `PrfH E φ → Prf (impChain E φ)`, descargando las hipótesis una a una (`deduction_aux`). -/
theorem prf_impChain_of_prfH : ∀ (E : List Formula) {φ : Formula}, PrfH E φ → Prf (impChain E φ)
  | [], _, h => prfH_nil_to_prf h rfl
  | e :: E, _, h => prf_impChain_of_prfH E (deduction_aux h e E rfl)

/-- Y de vuelta, en cualquier contexto que contenga E: con las hipótesis y MP. -/
theorem prfH_of_impChain (Γ : List Formula) :
    ∀ (E : List Formula) {φ : Formula}, (∀ e, List.Mem e E → List.Mem e Γ) → PrfH Γ (impChain E φ) → PrfH Γ φ
  | [], _, _, h => h
  | e :: E, φ, hsub, h =>
      have h' : PrfH Γ (e ⇒ φ) :=
        prfH_of_impChain Γ E (fun x hx => hsub x (List.Mem.tail e hx)) h
      PrfH.mp Γ e φ h' (PrfH.hyp Γ e (hsub e (List.Mem.head E)))

/-- ⭐ **El cálculo de T+E ES el de T, por reducción:** `PrfH E φ ↔ Prf (impChain E φ)`. -/
theorem prfH_iff_prf_impChain (E : List Formula) (φ : Formula) : PrfH E φ ↔ Prf (impChain E φ) :=
  ⟨prf_impChain_of_prfH E, fun h => prfH_of_impChain E E (fun _ hx => hx) (prf_to_prfH h E)⟩

/-! ## §2 · El código de `impChain`, y el predicado de prueba de T+E -/

/-- El código de `impChain E φ` como TÉRMINO con un hueco `x` en lugar del código de φ. -/
def impChainC : List Formula → Term → Term
  | [], x => x
  | e :: E, x => impChainC E (implc (formCode e) x)

/-- ⭐ `formCode (impChain E φ) = impChainC E (formCode φ)`, por definición. -/
theorem formCode_impChain : ∀ (E : List Formula) (φ : Formula), formCode (impChain E φ) = impChainC E (formCode φ)
  | [], _ => rfl
  | e :: E, φ => by
      have hc : formCode (e ⇒ φ) = implc (formCode e) (formCode φ) := rfl
      show formCode (impChain E (e ⇒ φ)) = impChainC E (implc (formCode e) (formCode φ))
      rw [← hc]
      exact formCode_impChain E (e ⇒ φ)

theorem formCode_neg (φ : Formula) : formCode (neg φ) = implc (formCode φ) botc := rfl

/-- El predicado de prueba de T+E (ADR‑144 §3): `y` es, en T, una prueba de la implicación de E a `x`. -/
def PfE (E : List Formula) (y x : Term) : Formula := PfF y (impChainC E x)

/-- 🏁 **PosNum de T+E**: lo que T+E demuestra tiene una prueba cuyo código es un numeral. -/
theorem posNumE {E : List Formula} {φ : Formula} (h : PrfH E φ) :
    ∃ m : Nat, Prf (PfE E (numeralM m) (formCode φ)) := by
  obtain ⟨m, hm⟩ := posNum ((prfH_iff_prf_impChain E φ).1 h)
  rw [formCode_impChain] at hm
  exact ⟨m, hm⟩

/-- 🏁 **NegNum de T+E**: si T+E no demuestra φ, T refuta cada candidata a prueba de φ en T+E. -/
theorem negNumE {E : List Formula} {φ : Formula} (h : ¬ PrfH E φ) (m : Nat) :
    Prf (neg (PfE E (numeralM m) (formCode φ))) := by
  have hm := negNum_formCode (fun hp => h ((prfH_iff_prf_impChain E φ).2 hp)) m
  rw [formCode_impChain] at hm
  exact hm

/-! ### El código de la conclusión, por otro igual en T -/

theorem prf_congr_implc_left {a b y : Term} (h : Prf (a =eq b)) : Prf (implc a y =eq implc b y) :=
  prf_congr_bin1 h

theorem prf_congr_impChainC : ∀ (E : List Formula) {a b : Term}, Prf (a =eq b) →
    Prf (impChainC E a =eq impChainC E b)
  | [], _, _, h => h
  | e :: E, a, b, h => by
      show Prf (impChainC E (implc (formCode e) a) =eq impChainC E (implc (formCode e) b))
      exact prf_congr_impChainC E (prf_congr_bin2 h)

theorem prf_PfE_imp (E : List Formula) (y : Term) {a b : Term} (h : Prf (a =eq b)) :
    Prf (PfE E y a ⇒ PfE E y b) := by
  refine prf_deduction ?_
  have hh := prfH_hyp_self (PfF y (impChainC E a))
  exact PrfH_and_intro (PrfH_and_elim_left hh)
    (PrfH_congr_In_left (prf_to_prfH (prf_congr_impChainC E h) _) (PrfH_and_elim_right hh))

theorem prf_PfE_congr {E : List Formula} {y a b : Term} (h : Prf (a =eq b)) (hp : Prf (PfE E y a)) :
    Prf (PfE E y b) :=
  prf_mp (prf_PfE_imp E y h) hp

theorem prf_neg_PfE_congr {E : List Formula} {y a b : Term} (h : Prf (a =eq b))
    (hp : Prf (neg (PfE E y a))) : Prf (neg (PfE E y b)) := by
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH hp _)
    (PrfH.mp _ _ _ (prf_to_prfH (prf_PfE_imp E y (prf_eq_symm h)) _) (prfH_hyp_self _))

/-! ## §3 · La sentencia de Rosser -/

/-! ### Sustitución y lift: `impChainC` y `PfE` dejan pasar los dos, porque los códigos de E son cerrados -/

theorem substTerm_implc (v : Nat) (s a b : Term) :
    substTerm v s (implc a b) = implc (substTerm v s a) (substTerm v s b) := rfl
theorem liftTerm_implc (c : Nat) (a b : Term) :
    liftTerm c (implc a b) = implc (liftTerm c a) (liftTerm c b) := rfl
theorem substTerm_botc (v : Nat) (s : Term) : substTerm v s botc = botc := rfl
theorem liftTerm_botc (c : Nat) : liftTerm c botc = botc := rfl

theorem substTerm_impChainC (v : Nat) (s : Term) : ∀ (E : List Formula) (x : Term),
    substTerm v s (impChainC E x) = impChainC E (substTerm v s x)
  | [], _ => rfl
  | e :: E, x => by
      show substTerm v s (impChainC E (implc (formCode e) x)) = impChainC E (implc (formCode e) (substTerm v s x))
      rw [substTerm_impChainC v s E, substTerm_implc, ROBINSON_PlusPlus.Meta.LiftcCodePrf.substTerm_formCode]

theorem liftTerm_impChainC (c : Nat) : ∀ (E : List Formula) (x : Term),
    liftTerm c (impChainC E x) = impChainC E (liftTerm c x)
  | [], _ => rfl
  | e :: E, x => by
      show liftTerm c (impChainC E (implc (formCode e) x)) = impChainC E (implc (formCode e) (liftTerm c x))
      rw [liftTerm_impChainC c E, liftTerm_implc, ROBINSON_PlusPlus.Meta.DerivCondPrf.liftTerm_formCode]

theorem substFormula_PfE (v : Nat) (s : Term) (E : List Formula) (y x : Term) :
    substFormula v s (PfE E y x) = PfE E (substTerm v s y) (substTerm v s x) := by
  show substFormula v s (PfF y (impChainC E x)) = PfF (substTerm v s y) (impChainC E (substTerm v s x))
  rw [← substTerm_impChainC]
  rfl

theorem liftFormula_PfE (c : Nat) (E : List Formula) (y x : Term) :
    liftFormula c (PfE E y x) = PfE E (liftTerm c y) (liftTerm c x) := by
  show liftFormula c (PfF y (impChainC E x)) = PfF (liftTerm c y) (impChainC E (liftTerm c x))
  rw [← liftTerm_impChainC]
  rfl

/-! ### ρ_E, su cuerpo, y la sentencia -/

/-- ρ_E(x), con `x = #0`: toda prueba de x en T+E tiene DELANTE una prueba de ¬x. Bajo el `∀`, `#0` es `y` y `#1` es
    `x`; bajo el `∃`, `#0` es `z`, `#1` es `y` y `#2` es `x`. -/
def rhoE (E : List Formula) : Formula :=
  Formula.forall (Formula.impl (PfE E (.var 0) (.var 1))
    (Formula.ex (land (lt (.var 0) (.var 1)) (PfE E (.var 0) (implc (.var 2) botc)))))

/-- El cuerpo de ρ_E(c), con `c` cerrado: `Pf_E(y, c) → ∃z (z < y ∧ Pf_E(z, ¬c))`, con `y = #0`. -/
def rhoBody (E : List Formula) (c : Term) : Formula :=
  Formula.impl (PfE E (.var 0) c) (Formula.ex (land (lt (.var 0) (.var 1)) (PfE E (.var 0) (implc c botc))))

/-- 🏁 **La sentencia de Rosser de T+E**: el punto fijo de ρ_E. -/
noncomputable def R (E : List Formula) : Formula := selfAppN (diagBeta (rhoE E))

theorem subst_rhoE (E : List Formula) (c : Term) (hl : liftTerm 0 c = c) :
    substFormula 0 c (rhoE E) = Formula.forall (rhoBody E c) := by
  simp only [rhoE, rhoBody, substFormula, substFormula_PfE, land, lt, substTerms, substTerm, substTerm_implc,
    substTerm_botc, hl]
  rfl

/-- ρ_E(c) instanciada en un término cerrado `t`: `Pf_E(t, c) → ∃z (z < t ∧ Pf_E(z, ¬c))`. -/
theorem subst_rhoBody (E : List Formula) {c : Term} (hc : ∀ v s, substTerm v s c = c) (t : Term)
    (ht : liftTerm 0 t = t) :
    substFormula 0 t (rhoBody E c) =
      Formula.impl (PfE E t c) (Formula.ex (land (lt (.var 0) t) (PfE E (.var 0) (implc c botc)))) := by
  simp only [rhoBody, substFormula, substFormula_PfE, land, lt, substTerms, substTerm, substTerm_implc,
    substTerm_botc, hc, ht]
  rfl

theorem subst_PfE_var0 (E : List Formula) {x : Term} (hx : ∀ v s, substTerm v s x = x) (t : Term) :
    substFormula 0 t (PfE E (.var 0) x) = PfE E t x := by
  rw [substFormula_PfE, hx]
  rfl

theorem subst_negPfE (E : List Formula) {x : Term} (hx : ∀ v s, substTerm v s x = x) (t : Term) :
    substFormula 0 t (neg (PfE E (.var 0) x)) = neg (PfE E t x) := by
  show Formula.impl (substFormula 0 t (PfE E (.var 0) x)) Formula.bottom = Formula.impl (PfE E t x) Formula.bottom
  rw [subst_PfE_var0 E hx]

theorem subst_lt_negPfE (E : List Formula) {x b : Term} (hx : ∀ v s, substTerm v s x = x)
    (hb : ∀ v s, substTerm v s b = b) :
    substFormula 0 (.var 0) (Formula.impl (lt (.var 0) b) (neg (PfE E (.var 0) x))) =
      Formula.impl (lt (.var 0) b) (neg (PfE E (.var 0) x)) := by
  show Formula.impl (lt (substTerm 0 (.var 0) (.var 0)) (substTerm 0 (.var 0) b))
      (substFormula 0 (.var 0) (neg (PfE E (.var 0) x))) = _
  rw [subst_negPfE E hx, hb]
  rfl

/-- El testigo: `(z < y ∧ Pf_E(z, x))[z := t] = (t < y ∧ Pf_E(t, x))`, con `y`, que era `#1`, ya `#0`. -/
theorem subst_witness (E : List Formula) {x : Term} (hx : ∀ v s, substTerm v s x = x) (t : Term) :
    substFormula 0 t (land (lt (.var 0) (.var 1)) (PfE E (.var 0) x)) = land (lt t (.var 0)) (PfE E t x) := by
  show land (substFormula 0 t (lt (.var 0) (.var 1))) (substFormula 0 t (PfE E (.var 0) x)) = _
  rw [subst_PfE_var0 E hx]
  rfl

theorem liftFormula_one_rhoE (E : List Formula) : liftFormula 1 (rhoE E) = rhoE E := by
  simp only [rhoE, liftFormula, liftFormula_PfE, land, lt, liftTerms, liftTerm, liftTerm_implc, liftTerm_botc]
  rfl

/-- La sentencia de Rosser es una SENTENCIA (la prueba de `liar_isSentence`). -/
theorem R_isSentence (E : List Formula) : IsSentence (R E) := by
  have hβ : liftFormula (0 + 1) (diagBeta (rhoE E)) = diagBeta (rhoE E) :=
    diagBeta_lift1 (liftFormula_one_rhoE E)
  show liftFormula 0 (substFormula 0 (numeral (codeNat (diagBeta (rhoE E)))) (diagBeta (rhoE E)))
     = substFormula 0 (numeral (codeNat (diagBeta (rhoE E)))) (diagBeta (rhoE E))
  rw [FOL.Lift0.liftFormula_subst _ 0 0 (Nat.le_refl 0),
    ROBINSON_PlusPlus.Meta.DerivCondPrf.liftTerm_numeral, hβ]

/-- El punto fijo, con ρ ya instanciada en ⌜R⌝: `R ⇔ ∀y (Pf_E(y, ⌜R⌝) → ∃z (z < y ∧ Pf_E(z, ⌜¬R⌝)))`. -/
theorem prf_R_fix (E : List Formula) : Prf (R E ⇔ Formula.forall (rhoBody E (numeral (codeNat (R E))))) := by
  have fp : Prf (R E ⇔ substFormula 0 (numeral (codeNat (R E))) (rhoE E)) := prf_diagonal (rhoE E)
  rw [subst_rhoE E _ (ROBINSON_PlusPlus.Meta.DerivCondPrf.liftTerm_numeral 0 _)] at fp
  exact fp

/-- ⌜R⌝, como lo da `formCode` y como lo da el punto fijo, es el mismo en T. -/
theorem prf_codeR (E : List Formula) : Prf (formCode (R E) =eq numeral (codeNat (R E))) :=
  ROBINSON_PlusPlus.Meta.CodeNumeralPrf.prf_formCode_numeral (R E)

theorem substTerm_codeR (E : List Formula) (v : Nat) (s : Term) :
    substTerm v s (numeral (codeNat (R E))) = numeral (codeNat (R E)) :=
  ROBINSON_PlusPlus.Meta.DerivCondPrf.substTerm_numeral v s _

/-! ## §4 · El argumento -/

/-- `∀z<b ¬B(z)` refuta `∃z (z < b ∧ B(z))`. -/
theorem prf_neg_ex_lt {b : Term} {B : Formula}
    (hself : substFormula 0 (.var 0) (Formula.impl (lt (.var 0) b) (neg B)) = Formula.impl (lt (.var 0) b) (neg B))
    (h : Prf (Formula.forall (Formula.impl (lt (.var 0) b) (neg B)))) :
    Prf (Formula.ex (land (lt (.var 0) b) B) ⇒ Formula.bottom) := by
  have h0 : Prf (Formula.impl (lt (.var 0) b) (neg B)) := by
    have h1 := prf_spec h (.var 0)
    rw [hself] at h1
    exact h1
  refine prf_ex_elim_imp ?_
  have hh := prfH_hyp_self (land (lt (.var 0) b) B)
  exact PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH h0 _) (PrfH_and_elim_left hh)) (PrfH_and_elim_right hh)

/-- (a), el paso: si T+E prueba ρ_E(c), m̄ es una prueba de c en T+E y T refuta cada candidata a prueba de ¬c, T+E es
    inconsistente. -/
theorem prfH_bot_of {E : List Formula} {c : Term} (hc : ∀ v s, substTerm v s c = c) (m : Nat)
    (hρ : PrfH E (Formula.forall (rhoBody E c))) (hm : Prf (PfE E (numeralM m) c))
    (hneg : ∀ k : Nat, Prf (neg (PfE E (numeralM k) (implc c botc)))) :
    PrfH E Formula.bottom := by
  have hnc : ∀ v s, substTerm v s (implc c botc) = implc c botc := fun v s => by
    rw [substTerm_implc, hc, substTerm_botc]
  have hinst : PrfH E (substFormula 0 (numeralM m) (rhoBody E c)) :=
    PrfH.mp _ _ _ (PrfH.incl0 E _ (Prfᵢ.q1 (rhoBody E c) (numeralM m))) hρ
  rw [subst_rhoBody E hc (numeralM m) (ROBINSON_PlusPlus.Minimal.Axioms.liftTerm_numeralM 0 m)] at hinst
  have hex := PrfH.mp _ _ _ hinst (prf_to_prfH hm E)
  have hall : Prf (Formula.forall (Formula.impl (lt (.var 0) (numeralM m)) (neg (PfE E (.var 0) (implc c botc))))) :=
    prf_bdAll_numeral _ (subst_negPfE E hnc (.var 0)) m (fun k _ => by rw [subst_negPfE E hnc]; exact hneg k)
  exact PrfH.mp _ _ _
    (prf_to_prfH (prf_neg_ex_lt (subst_lt_negPfE E hnc (fun v s => substTerm_numeralM v s m)) hall) E) hex

/-- (b), el paso: si m̄ es una prueba de ¬c en T+E y T refuta cada candidata a prueba de c, T prueba el cuerpo de
    ρ_E(c), con `y = #0` libre, por la tricotomía de `y` y m̄. -/
theorem prf_rhoBody_of {E : List Formula} {c : Term} (hc : ∀ v s, substTerm v s c = c) (m : Nat)
    (hm : Prf (PfE E (numeralM m) (implc c botc)))
    (hneg : ∀ k : Nat, Prf (neg (PfE E (numeralM k) c))) :
    Prf (rhoBody E c) := by
  have hnc : ∀ v s, substTerm v s (implc c botc) = implc c botc := fun v s => by
    rw [substTerm_implc, hc, substTerm_botc]
  have hall : Prf (Formula.forall (Formula.impl (lt (.var 0) (numeralM m)) (neg (PfE E (.var 0) c)))) :=
    prf_bdAll_numeral _ (subst_negPfE E hc (.var 0)) m (fun k _ => by rw [subst_negPfE E hc]; exact hneg k)
  have h0 : Prf (Formula.impl (lt (.var 0) (numeralM m)) (neg (PfE E (.var 0) c))) := by
    have h1 := prf_spec hall (.var 0)
    rw [subst_lt_negPfE E hc (fun v s => substTerm_numeralM v s m)] at h1
    exact h1
  refine prf_deduction ?_
  refine PrfH_or_elim (prf_to_prfH (ROBINSON_PlusPlus.Meta.NatMulPrf.prf_lt_trichotomy (.var 0) (numeralM m)) _)
    ?_ ?_
  · -- y < m̄: NegNum, por debajo de m̄
    exact PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prfᵢ.efq _))
      (PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH h0 _) (PrfH.hyp _ _ (List.Mem.head _)))
        (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))))
  · refine PrfH_or_elim (PrfH.hyp _ _ (List.Mem.head _)) ?_ ?_
    · -- y = m̄: NegNum, en m̄
      have hH : PrfH ((.var 0 =eq numeralM m) :: lor (.var 0 =eq numeralM m) (lt (numeralM m) (.var 0)) ::
          [PfE E (.var 0) c]) (substFormula 0 (.var 0) (PfE E (.var 0) c)) := by
        rw [subst_PfE_var0 E hc]
        exact PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
      have h2 := PrfH_leibniz_subst (PrfH.hyp _ _ (List.Mem.head _)) hH
      rw [subst_PfE_var0 E hc] at h2
      exact PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prfᵢ.efq _)) (PrfH.mp _ _ _ (prf_to_prfH (hneg m) _) h2)
    · -- m̄ < y: m̄ es el testigo
      refine PrfH_ex_intro (numeralM m) ?_
      rw [subst_witness E hnc]
      exact PrfH_and_intro (PrfH.hyp _ _ (List.Mem.head _)) (prf_to_prfH hm _)

/-- (a) Si T+E es consistente, no demuestra R. -/
theorem rosser_no_R (E : List Formula) (hcon : ¬ PrfH E Formula.bottom) : ¬ PrfH E (R E) := by
  intro hR
  obtain ⟨m, hm⟩ := posNumE hR
  have hnot : ¬ PrfH E (neg (R E)) := fun hN => hcon (PrfH.mp _ _ _ hN hR)
  refine hcon (prfH_bot_of (substTerm_codeR E) m ?_ (prf_PfE_congr (prf_codeR E) hm) fun k => ?_)
  · exact PrfH.mp _ _ _ (prf_to_prfH (prf_and_elim_left (prf_R_fix E)) E) hR
  · have hk := negNumE hnot k
    rw [formCode_neg] at hk
    exact prf_neg_PfE_congr (prf_congr_implc_left (prf_codeR E)) hk

/-- (b) Si T+E es consistente, no demuestra ¬R. -/
theorem rosser_no_negR (E : List Formula) (hcon : ¬ PrfH E Formula.bottom) : ¬ PrfH E (neg (R E)) := by
  intro hN
  obtain ⟨m, hm⟩ := posNumE hN
  rw [formCode_neg] at hm
  have hnot : ¬ PrfH E (R E) := fun hR => hcon (PrfH.mp _ _ _ hN hR)
  have hbody := prf_rhoBody_of (substTerm_codeR E) m (prf_PfE_congr (prf_congr_implc_left (prf_codeR E)) hm)
    (fun k => prf_neg_PfE_congr (prf_codeR E) (negNumE hnot k))
  have hRp : Prf (R E) := prf_mp (prf_and_elim_right (prf_R_fix E)) (Prf.gen _ hbody)
  exact hcon (PrfH.mp _ _ _ hN (prf_to_prfH hRp E))

/-! ## §5 · Los titulares -/

/-- 🏁 **ROSSER por la reducción, para TODA lista E**: si `PrfH E` es consistente, no decide `R E`. -/
theorem rosser_red (E : List Formula) (hcon : ¬ PrfH E Formula.bottom) :
    And (¬ PrfH E (R E)) (¬ PrfH E (neg (R E))) :=
  ⟨rosser_no_R E hcon, rosser_no_negR E hcon⟩

/-- 🏁🏁 **ROSSER para las extensiones finitas T+E** (el enunciado de ADR‑145): si T+E es consistente, su sentencia de
    Rosser es INDECIDIBLE en T+E. `_hE` (E son sentencias) es lo que hace de `PrfH E` la teoría T+E; la prueba no la
    usa (`rosser_red`). -/
theorem rosser_ext (E : List Formula) (_hE : ∀ φ, List.Mem φ E → IsSentence φ) (hcon : ¬ PrfH E Formula.bottom) :
    And (¬ PrfH E (R E)) (¬ PrfH E (neg (R E))) :=
  rosser_red E hcon

/-- 🏁 **ROSSER para T, sin hipótesis** (con `consistencia`): ni `R []` ni `¬R []` son teoremas. -/
theorem rosser : And (¬ Prf (R [])) (¬ Prf (neg (R []))) := by
  have h := rosser_ext [] (fun _ hm => nomatch hm)
    (fun hb => ROBINSON_PlusPlus.Meta.Consistencia.consistencia (prfH_nil_to_prf hb rfl))
  exact ⟨fun hp => h.1 (prf_to_prfH hp []), fun hp => h.2 (prf_to_prfH hp [])⟩

/-! ## §6 · Los controles (CRI‑02, ADR‑144 §3) -/

/-- ✅ La hipótesis puede FALLAR: T+[⊥] es inconsistente… -/
theorem inconsistente_bottom : PrfH [Formula.bottom] Formula.bottom :=
  PrfH.hyp _ _ (List.Mem.head _)

/-- ✅ …y entonces la conclusión falla: T+[⊥] demuestra su sentencia de Rosser. La hipótesis no es de adorno. -/
theorem control_bottom : PrfH [Formula.bottom] (R [Formula.bottom]) :=
  PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prfᵢ.efq _)) inconsistente_bottom

/-- ✅ La hipótesis puede VALER en una extensión NO sólida: T+¬Con es consistente (por Gödel II y la deducción), y
    demuestra ¬Con, FALSA en el modelo (`con_verdadera`). -/
theorem consistente_neg_con :
    ¬ PrfH [neg ROBINSON_PlusPlus.Meta.GodelTwo.consistencyFormula'] Formula.bottom := by
  intro h
  have hnn : Prf (neg (neg ROBINSON_PlusPlus.Meta.GodelTwo.consistencyFormula')) :=
    (prfH_iff_prf_impChain _ _).1 h
  exact ROBINSON_PlusPlus.Meta.Consistencia.goedel_II
    (Prf.mp _ _ (Prf.p3 ROBINSON_PlusPlus.Meta.GodelTwo.consistencyFormula') hnn)

/-- ¬Con es una sentencia: T+¬Con es un miembro de la familia de `rosser_ext`. -/
theorem negCon_isSentence : IsSentence (neg ROBINSON_PlusPlus.Meta.GodelTwo.consistencyFormula') := by
  unfold IsSentence ROBINSON_PlusPlus.Meta.GodelTwo.consistencyFormula' ROBINSON_PlusPlus.Meta.ProofChain.provCodeC'
  rfl

/-- ✅ Y allí Rosser vale, por el titular: con E = [¬Con] las dos hipótesis de `rosser_ext` valen a la vez, y la
    sentencia de Rosser de T+¬Con es indecidible en T+¬Con, donde la solidez no puede sustituir a la consistencia. -/
theorem control_neg_con :
    And (¬ PrfH [neg ROBINSON_PlusPlus.Meta.GodelTwo.consistencyFormula']
        (R [neg ROBINSON_PlusPlus.Meta.GodelTwo.consistencyFormula']))
      (¬ PrfH [neg ROBINSON_PlusPlus.Meta.GodelTwo.consistencyFormula']
        (neg (R [neg ROBINSON_PlusPlus.Meta.GodelTwo.consistencyFormula']))) :=
  rosser_ext _ (fun φ h => by
      cases h with
      | head => exact negCon_isSentence
      | tail _ h' => cases h') consistente_neg_con

end ROBINSON_PlusPlus.Meta.Rosser

#print axioms ROBINSON_PlusPlus.Meta.Rosser.prfH_iff_prf_impChain
#print axioms ROBINSON_PlusPlus.Meta.Rosser.formCode_impChain
#print axioms ROBINSON_PlusPlus.Meta.Rosser.posNumE
#print axioms ROBINSON_PlusPlus.Meta.Rosser.negNumE
#print axioms ROBINSON_PlusPlus.Meta.Rosser.R_isSentence
#print axioms ROBINSON_PlusPlus.Meta.Rosser.rosser_red
#print axioms ROBINSON_PlusPlus.Meta.Rosser.rosser_ext
#print axioms ROBINSON_PlusPlus.Meta.Rosser.rosser

/-! T08 en el módulo (ADR‑147): lo de Rosser no nombra la semántica; `rosser`, que descarga la hipótesis con
    `consistencia`, y el control de T+¬Con, que pasa por `goedel_II`, sí. -/
#pureza ROBINSON_PlusPlus.Meta.Rosser.prfH_iff_prf_impChain ROBINSON_PlusPlus.Meta.Rosser.formCode_impChain
  ROBINSON_PlusPlus.Meta.Rosser.posNumE ROBINSON_PlusPlus.Meta.Rosser.negNumE
  ROBINSON_PlusPlus.Meta.Rosser.R_isSentence ROBINSON_PlusPlus.Meta.Rosser.rosser_red
  ROBINSON_PlusPlus.Meta.Rosser.rosser_ext ROBINSON_PlusPlus.Meta.Rosser.control_bottom
  | ROBINSON_PlusPlus.Meta.Rosser.rosser ROBINSON_PlusPlus.Meta.Rosser.control_neg_con

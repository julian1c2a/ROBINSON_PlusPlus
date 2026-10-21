/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.RosserGuardNeg
import ROBINSON_PlusPlus.Meta.SubstfcWitnessPrf
import ROBINSON_PlusPlus.Meta.HasWitTcFnPrf
import ROBINSON_PlusPlus.Meta.Representability2Prf

/-!
# `Meta/RosserNegLinea.lean` — Rosser, etapa 4: NegLineWF, la línea mala se refuta (ADR‑146 §3, ADR‑147, ADR‑154)

**Qué.** Para el numeral de cualquier línea, la buena formación decidida:

    lineWF_decide x : lineWFN Vax x ∨ Prf (¬ lineWF x̄)
    prf_neg_lineWF  : ¬ lineWFN Vax x → Prf (¬ lineWF x̄)

con `Vax = codeNatList axioms`, el valor de `axiomsCodeT` (el ancla, `prf_ancla`).

* **§1** Los combinadores: la composición bajo dos hipótesis y el rechazo por cada mitad de una conjunción.
* **§2** Las 21 instancias de `ax_lineWF_k` en una línea cualquiera `X`, en la dirección directa: con la etiqueta `k`,
  `lineWF X` da la RHS de su regla (`axL_p1`…`axL_listInd`). Las RHS están copiadas de `Minimal/Axioms.lean` con
  `(.var 0) ↦ X`, y las comprueba el núcleo: cada una cierra por definición con la instancia del axioma.
* **§3** La evaluación de las reconstrucciones sobre el numeral: los constructores de código (`evImpl`…), la
  sustitución y el lift con las guardas verdaderas (NumEval), los códigos cerrados de `ind`/`listInd` (`evTC`), y el
  ancla, para `thy` (`prf_not_In_axiomsCodeT`).
* **§4** Una rama de la inversión (`Rama x k`) cae por la longitud, por la etiqueta o por su RHS, y se decide
  (`refT_of`).
* **§5** Las 21 reglas, una por una (`refT_p1`…`refT_listInd`): las guardas se deciden con GuardNeg, y la conclusión
  se compara, evaluada, con la de ℕ.
* **§6** El ensamblaje por la inversión (`ax_lineWF_inv`): `lineWF_decide`, `prf_neg_lineWF`.

**De dónde.** La inversión es `prf_lineWF_inv` (`Meta/Sigma1AtomPrf.lean`); las guardas, GuardNeg (ADR‑153); la
evaluación de la sustitución, NumEval (ADR‑152); el espejo en ℕ, `lineWFT` de `ModeloCodigo`. Los envoltorios de
`Meta/LineWFCases.lean` y `Meta/ChainNegPrf.lean` (retirado en ADR‑160) trabajan sobre líneas EXPLÍCITAS; aquí la
línea es un numeral, y las
RHS con accesores (`lenc`, `carc`, `nthc`) se evalúan sobre él.

**Controles.** `control_neg_lineWF_zero`: el `0` no es una línea. Y `control_exacta` (con la solidez en `MNV V₀`):
donde la línea es buena en ℕ, `Prf` no la refuta. Es el control positivo del `#pureza`.

⛔ Ningún numeral se evalúa: `numeralM (codeNatList axioms)`, astronómico, sólo se mueve por lemas ∀ (la lista de
`axioms` por `prf_listFormCodeM_numeral`, sin desplegar).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open FOL ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Hilbert ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ChainPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs
open ROBINSON_PlusPlus.Meta.ModeloCodigo ROBINSON_PlusPlus.Meta.RosserNumerales ROBINSON_PlusPlus.Meta.RosserNumEval
open ROBINSON_PlusPlus.Meta.RosserGuardNeg

namespace ROBINSON_PlusPlus.Meta.RosserNegLinea

/-- El valor de `axiomsCodeT`: el código de los 142 (ADR‑148). -/
abbrev Vax : Nat := codeNatList axioms

/-! ## §1 · Los combinadores -/

theorem imp2_post {A B E C : Formula} (hAB : Prf (A ⇒ (B ⇒ E))) (hE : Prf (E ⇒ C)) : Prf (A ⇒ (B ⇒ C)) := by
  refine prf_deduction (deduction_aux (Δ := [B, A]) ?_ B [A] rfl)
  exact PrfH.mp _ _ _ (prf_to_prfH hE _) (PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH hAB _)
    (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))) (PrfH.hyp _ _ (List.Mem.head _)))

theorem rejL {A B : Formula} (h : Prf (A ⇒ Formula.bottom)) : Prf (Formula.and A B ⇒ Formula.bottom) :=
  impT (Prf.incl (Prfᵢ.c2 _ _)) h

theorem rejR {A B : Formula} (h : Prf (B ⇒ Formula.bottom)) : Prf (Formula.and A B ⇒ Formula.bottom) :=
  impT (Prf.incl (Prfᵢ.c3 _ _)) h

/-- La hermana de `crit_tag_absurd` para una casilla cualquiera. -/
theorem crit_nth_absurd (X : Term) (i k m : Nat) (hkm : k ≠ m) (hX : Prf (nthc X (numeralM i) =eq numeralM k)) :
    Prf ((nthc X (numeralM i) =eq numeralM m) ⇒ Formula.bottom) :=
  prf_deduction (PrfH.mp _ _ _ (prf_to_prfH (crit_num_ne k m hkm) _)
    (PrfH_eq_trans (prf_to_prfH (prf_eq_symm hX) _) (prfH_hyp_self _)))

/-! ## §2 · Las 21 instancias de `ax_lineWF_k`, en la dirección directa -/

/-- Con la etiqueta `k`, `lineWF X` da la RHS de su regla instanciada en `X`. -/
theorem prf_lineWF_rhs {k : Nat} {D : Formula} (X : Term)
    (hax : Prf (Formula.forall (Formula.impl (nthc (.var 0) (succ zero) =eq numeralM k) (lineWF (.var 0) ⇔ D)))) :
    Prf ((nthc X (succ zero) =eq numeralM k) ⇒ (lineWF X ⇒ substFormula 0 X D)) := by
  have hh := prf_spec hax X
  have e : substFormula 0 X (Formula.impl (nthc (.var 0) (succ zero) =eq numeralM k) (lineWF (.var 0) ⇔ D)) =
      Formula.impl (nthc X (succ zero) =eq numeralM k) (lineWF X ⇔ substFormula 0 X D) := by
    simp only [substFormula, iff, nthc, succ, zero, lineWF, substTerm, substTerms, substTerm_numeralM, ite_true]
  rw [e] at hh
  exact impT hh (Prf.incl (Prfᵢ.c2 _ _))

theorem axL_p1 (X : Term) : Prf ((nthc X (succ zero) =eq numeralM 0) ⇒ (lineWF X ⇒
    Formula.and (lenc X =eq numeralM 4) ((carc X) =eq implc (nthc X (numeralM 2)) (implc (nthc X (numeralM 3)) (nthc X (numeralM 2)))))) := by
  have h := prf_lineWF_rhs X (prf_ax (show ax_lineWF_p1 ∈ axioms by simp [axioms]))
  exact h

theorem axL_p2 (X : Term) : Prf ((nthc X (succ zero) =eq numeralM 1) ⇒ (lineWF X ⇒
    Formula.and (lenc X =eq numeralM 5) ((carc X) =eq implc (implc (nthc X (numeralM 2)) (implc (nthc X (numeralM 3)) (nthc X (numeralM 4)))) (implc (implc (nthc X (numeralM 2)) (nthc X (numeralM 3))) (implc (nthc X (numeralM 2)) (nthc X (numeralM 4))))))) := by
  have h := prf_lineWF_rhs X (prf_ax (show ax_lineWF_p2 ∈ axioms by simp [axioms]))
  exact h

theorem axL_c1 (X : Term) : Prf ((nthc X (succ zero) =eq numeralM 2) ⇒ (lineWF X ⇒
    Formula.and (lenc X =eq numeralM 4) ((carc X) =eq implc (nthc X (numeralM 2)) (implc (nthc X (numeralM 3)) (andc (nthc X (numeralM 2)) (nthc X (numeralM 3))))))) := by
  have h := prf_lineWF_rhs X (prf_ax (show ax_lineWF_c1 ∈ axioms by simp [axioms]))
  exact h

theorem axL_c2 (X : Term) : Prf ((nthc X (succ zero) =eq numeralM 3) ⇒ (lineWF X ⇒
    Formula.and (lenc X =eq numeralM 4) ((carc X) =eq implc (andc (nthc X (numeralM 2)) (nthc X (numeralM 3))) (nthc X (numeralM 2))))) := by
  have h := prf_lineWF_rhs X (prf_ax (show ax_lineWF_c2 ∈ axioms by simp [axioms]))
  exact h

theorem axL_c3 (X : Term) : Prf ((nthc X (succ zero) =eq numeralM 4) ⇒ (lineWF X ⇒
    Formula.and (lenc X =eq numeralM 4) ((carc X) =eq implc (andc (nthc X (numeralM 2)) (nthc X (numeralM 3))) (nthc X (numeralM 3))))) := by
  have h := prf_lineWF_rhs X (prf_ax (show ax_lineWF_c3 ∈ axioms by simp [axioms]))
  exact h

theorem axL_j1 (X : Term) : Prf ((nthc X (succ zero) =eq numeralM 5) ⇒ (lineWF X ⇒
    Formula.and (lenc X =eq numeralM 4) ((carc X) =eq implc (nthc X (numeralM 2)) (orc (nthc X (numeralM 2)) (nthc X (numeralM 3)))))) := by
  have h := prf_lineWF_rhs X (prf_ax (show ax_lineWF_j1 ∈ axioms by simp [axioms]))
  exact h

theorem axL_j2 (X : Term) : Prf ((nthc X (succ zero) =eq numeralM 6) ⇒ (lineWF X ⇒
    Formula.and (lenc X =eq numeralM 4) ((carc X) =eq implc (nthc X (numeralM 3)) (orc (nthc X (numeralM 2)) (nthc X (numeralM 3)))))) := by
  have h := prf_lineWF_rhs X (prf_ax (show ax_lineWF_j2 ∈ axioms by simp [axioms]))
  exact h

theorem axL_j3 (X : Term) : Prf ((nthc X (succ zero) =eq numeralM 7) ⇒ (lineWF X ⇒
    Formula.and (lenc X =eq numeralM 5) ((carc X) =eq implc (orc (nthc X (numeralM 2)) (nthc X (numeralM 3))) (implc (implc (nthc X (numeralM 2)) (nthc X (numeralM 4))) (implc (implc (nthc X (numeralM 3)) (nthc X (numeralM 4))) (nthc X (numeralM 4))))))) := by
  have h := prf_lineWF_rhs X (prf_ax (show ax_lineWF_j3 ∈ axioms by simp [axioms]))
  exact h

theorem axL_efq (X : Term) : Prf ((nthc X (succ zero) =eq numeralM 8) ⇒ (lineWF X ⇒
    Formula.and (lenc X =eq numeralM 3) ((carc X) =eq implc (botc) (nthc X (numeralM 2))))) := by
  have h := prf_lineWF_rhs X (prf_ax (show ax_lineWF_efq ∈ axioms by simp [axioms]))
  exact h

theorem axL_q1 (X : Term) : Prf ((nthc X (succ zero) =eq numeralM 9) ⇒ (lineWF X ⇒
    Formula.and (lenc X =eq numeralM 4) (Formula.and (hasWitF (nthc X (numeralM 2))) (Formula.and (hasWit (nthc X (numeralM 3))) ((carc X) =eq implc (forallc (nthc X (numeralM 2))) (substfc (zero) (nthc X (numeralM 3)) (nthc X (numeralM 2)))))))) := by
  have h := prf_lineWF_rhs X (prf_ax (show ax_lineWF_q1 ∈ axioms by simp [axioms]))
  exact h

theorem axL_q2 (X : Term) : Prf ((nthc X (succ zero) =eq numeralM 10) ⇒ (lineWF X ⇒
    Formula.and (lenc X =eq numeralM 4) (Formula.and (hasWitF (nthc X (numeralM 2))) (Formula.and (hasWit (nthc X (numeralM 3))) ((carc X) =eq implc (substfc (zero) (nthc X (numeralM 3)) (nthc X (numeralM 2))) (exc (nthc X (numeralM 2)))))))) := by
  have h := prf_lineWF_rhs X (prf_ax (show ax_lineWF_q2 ∈ axioms by simp [axioms]))
  exact h

theorem axL_q3 (X : Term) : Prf ((nthc X (succ zero) =eq numeralM 11) ⇒ (lineWF X ⇒
    Formula.and (lenc X =eq numeralM 4) (Formula.and (hasWitF (nthc X (numeralM 3))) ((carc X) =eq implc (forallc (implc (nthc X (numeralM 2)) (liftfc (zero) (nthc X (numeralM 3))))) (implc (exc (nthc X (numeralM 2))) (nthc X (numeralM 3))))))) := by
  have h := prf_lineWF_rhs X (prf_ax (show ax_lineWF_q3 ∈ axioms by simp [axioms]))
  exact h

theorem axL_eqrefl (X : Term) : Prf ((nthc X (succ zero) =eq numeralM 12) ⇒ (lineWF X ⇒
    Formula.and (lenc X =eq numeralM 3) ((carc X) =eq eqc (nthc X (numeralM 2)) (nthc X (numeralM 2))))) := by
  have h := prf_lineWF_rhs X (prf_ax (show ax_lineWF_eqrefl ∈ axioms by simp [axioms]))
  exact h

theorem axL_leibniz (X : Term) : Prf ((nthc X (succ zero) =eq numeralM 13) ⇒ (lineWF X ⇒
    Formula.and (lenc X =eq numeralM 5) (Formula.and (hasWitF (nthc X (numeralM 2))) (Formula.and (hasWit (nthc X (numeralM 3))) (Formula.and (hasWit (nthc X (numeralM 4))) ((carc X) =eq implc (eqc (nthc X (numeralM 3)) (nthc X (numeralM 4))) (implc (substfc (zero) (nthc X (numeralM 3)) (nthc X (numeralM 2))) (substfc (zero) (nthc X (numeralM 4)) (nthc X (numeralM 2)))))))))) := by
  have h := prf_lineWF_rhs X (prf_ax (show ax_lineWF_leibniz ∈ axioms by simp [axioms]))
  exact h

theorem axL_p3 (X : Term) : Prf ((nthc X (succ zero) =eq numeralM 14) ⇒ (lineWF X ⇒
    Formula.and (lenc X =eq numeralM 3) ((carc X) =eq implc (implc (implc (nthc X (numeralM 2)) (botc)) (botc)) (nthc X (numeralM 2))))) := by
  have h := prf_lineWF_rhs X (prf_ax (show ax_lineWF_p3 ∈ axioms by simp [axioms]))
  exact h

theorem axL_thy (X : Term) : Prf ((nthc X (succ zero) =eq numeralM 15) ⇒ (lineWF X ⇒
    Formula.and (lenc X =eq numeralM 2) (In (carc X) axiomsCodeT))) := by
  have h := prf_lineWF_rhs X (prf_ax (show ax_lineWF_thy ∈ axioms by simp [axioms]))
  exact h

theorem axL_mp (X : Term) : Prf ((nthc X (succ zero) =eq numeralM 16) ⇒ (lineWF X ⇒
    (lenc X =eq numeralM 3))) := by
  have h := prf_lineWF_rhs X (prf_ax (show ax_lineWF_mp ∈ axioms by simp [axioms]))
  exact h

theorem axL_gen (X : Term) : Prf ((nthc X (succ zero) =eq numeralM 17) ⇒ (lineWF X ⇒
    Formula.and (lenc X =eq numeralM 3) ((carc X) =eq forallc (nthc X (numeralM 2))))) := by
  have h := prf_lineWF_rhs X (prf_ax (show ax_lineWF_gen ∈ axioms by simp [axioms]))
  exact h

set_option maxRecDepth 20000 in
theorem axL_ind (X : Term) : Prf ((nthc X (succ zero) =eq numeralM 18) ⇒ (lineWF X ⇒
    Formula.and (lenc X =eq numeralM 3) (Formula.and (hasWitF (nthc X (numeralM 2))) ((carc X) =eq implc (substfc (zero) (termCodeM zero) (nthc X (numeralM 2))) (implc (forallc (implc (nthc X (numeralM 2)) (substfc (zero) (termCodeM (succ (.var 0))) (liftfc (succ zero) (nthc X (numeralM 2)))))) (forallc (nthc X (numeralM 2)))))))) := by
  have h := prf_lineWF_rhs X (prf_ax (show ax_lineWF_ind ∈ axioms by simp [axioms]))
  exact h

theorem axL_qconf (X : Term) : Prf ((nthc X (succ zero) =eq numeralM 19) ⇒ (lineWF X ⇒
    Formula.and (lenc X =eq numeralM 4) (Formula.and (hasWitF (nthc X (numeralM 2))) ((carc X) =eq implc (forallc (implc (liftfc (zero) (nthc X (numeralM 2))) (nthc X (numeralM 3)))) (implc (nthc X (numeralM 2)) (forallc (nthc X (numeralM 3)))))))) := by
  have h := prf_lineWF_rhs X (prf_ax (show ax_lineWF_qconf ∈ axioms by simp [axioms]))
  exact h

set_option maxRecDepth 20000 in
theorem axL_listInd (X : Term) : Prf ((nthc X (succ zero) =eq numeralM 20) ⇒ (lineWF X ⇒
    Formula.and (lenc X =eq numeralM 3) (Formula.and (hasWitF (nthc X (numeralM 2))) ((carc X) =eq implc (substfc (zero) (termCodeM nil) (nthc X (numeralM 2))) (implc (forallc (forallc (implc (liftfc (succ zero) (nthc X (numeralM 2))) (substfc (zero) (termCodeM (cons (.var 1) (.var 0))) (liftfc (succ (succ zero)) (liftfc (succ zero) (nthc X (numeralM 2)))))))) (forallc (nthc X (numeralM 2)))))))) := by
  have h := prf_lineWF_rhs X (prf_ax (show ax_lineWF_listInd ∈ axioms by simp [axioms]))
  exact h

/-! ## §3 · La evaluación sobre el numeral -/

/-- La casilla `i` de `x̄`, dentro de la longitud de la regla. -/
theorem hN {x ℓ : Nat} (hl : lenN x = ℓ) (i : Nat) (hi : i < ℓ := by decide) :
    Prf (nthc (numeralM x) (numeralM i) =eq numeralM (nthN x i)) :=
  prf_nthc_numeral i x (by rw [hl]; exact hi)

theorem nz {x ℓ : Nat} (hl : lenN x = ℓ) (hℓ : ℓ ≠ 0 := by decide) : x ≠ 0 := ne_zero_of_lenN hl hℓ

theorem evImpl {A B : Term} {a b : Nat} (ha : Prf (A =eq numeralM a)) (hb : Prf (B =eq numeralM b)) :
    Prf (implc A B =eq numeralM (implcN a b)) :=
  prf_cons_evalM_of (prf_refl (numeralM 5)) (prf_cons_evalM_of ha (prf_cons_evalM_of hb (prf_refl (numeralM 0))))

theorem evAnd {A B : Term} {a b : Nat} (ha : Prf (A =eq numeralM a)) (hb : Prf (B =eq numeralM b)) :
    Prf (andc A B =eq numeralM (andcN a b)) :=
  prf_cons_evalM_of (prf_refl (numeralM 7)) (prf_cons_evalM_of ha (prf_cons_evalM_of hb (prf_refl (numeralM 0))))

theorem evOr {A B : Term} {a b : Nat} (ha : Prf (A =eq numeralM a)) (hb : Prf (B =eq numeralM b)) :
    Prf (orc A B =eq numeralM (orcN a b)) :=
  prf_cons_evalM_of (prf_refl (numeralM 8)) (prf_cons_evalM_of ha (prf_cons_evalM_of hb (prf_refl (numeralM 0))))

theorem evEqc {A B : Term} {a b : Nat} (ha : Prf (A =eq numeralM a)) (hb : Prf (B =eq numeralM b)) :
    Prf (eqc A B =eq numeralM (eqcN a b)) :=
  prf_cons_evalM_of (prf_refl (numeralM 4)) (prf_cons_evalM_of ha (prf_cons_evalM_of hb (prf_refl (numeralM 0))))

theorem evAll {A : Term} {a : Nat} (ha : Prf (A =eq numeralM a)) : Prf (forallc A =eq numeralM (forallcN a)) :=
  prf_cons_evalM_of (prf_refl (numeralM 6)) (prf_cons_evalM_of ha (prf_refl (numeralM 0)))

theorem evExc {A : Term} {a : Nat} (ha : Prf (A =eq numeralM a)) : Prf (exc A =eq numeralM (excN a)) :=
  prf_cons_evalM_of (prf_refl (numeralM 9)) (prf_cons_evalM_of ha (prf_refl (numeralM 0)))

/-- `substfc` evaluado sobre las casillas, con un código de fórmula y uno de término (NumEval). -/
theorem evSubst (v : Nat) {T A : Term} {t a : Nat} (hT : Prf (T =eq numeralM t)) (hA : Prf (A =eq numeralM a))
    (hFa : CodF a) (ht : CodT t) : Prf (substfc (numeralM v) T A =eq numeralM (substfcN v t a)) :=
  prf_eq_trans (prf_congr_substfc_arg2 hT) (prf_eq_trans (prf_congr_substfc_arg3 hA) (prf_substfc_numeral hFa v t ht))

/-- `liftfc` evaluado sobre una casilla, con un código de fórmula. -/
theorem evLift (c : Nat) {A : Term} {a : Nat} (hA : Prf (A =eq numeralM a)) (hFa : CodF a) :
    Prf (liftfc (numeralM c) A =eq numeralM (liftfcN c a)) :=
  prf_eq_trans (prf_congr_liftfc_arg2 hA) (prf_liftfc_numeral hFa c)

/-- Un código cerrado de término es el numeral de su valor (los de `ind` y `listInd`). -/
theorem evTC (t : Term) : Prf (termCodeM t =eq numeralM (codeNatTerm t)) := by
  have h := ROBINSON_PlusPlus.Meta.CodeNumeralPrf.prf_termCode_numeral t
  rw [← ROBINSON_PlusPlus.Meta.CheckArith.numeralM_eq, ← ROBINSON_PlusPlus.Meta.Representability.termCodeM_eq] at h
  exact h

theorem evForm (φ : Formula) : Prf (formCodeM φ =eq numeralM (codeNat φ)) := by
  have h := ROBINSON_PlusPlus.Meta.CodeNumeralPrf.prf_formCode_numeral φ
  rw [← ROBINSON_PlusPlus.Meta.CheckArith.numeralM_eq, ← ROBINSON_PlusPlus.Meta.Representability.formCodeM_eq] at h
  exact h

/-- El código de una lista de fórmulas es el numeral de su valor, por la lista: nada se evalúa. -/
theorem prf_listFormCodeM_numeral : ∀ L : List Formula, Prf (listFormCodeM L =eq numeralM (codeNatList L))
  | [] => prf_refl _
  | φ :: L => prf_cons_evalM_of (evForm φ) (prf_listFormCodeM_numeral L)

/-- 🏁 **Lo que no está entre los 142, `Prf` lo saca de `axiomsCodeT`** (por el ancla). -/
theorem prf_not_In_axiomsCodeT {y : Nat} (h : ¬ memN y Vax) :
    Prf ((In (numeralM y) axiomsCodeT) ⇒ Formula.bottom) := by
  have hA : Prf (axiomsCodeT =eq numeralM Vax) :=
    prf_eq_trans ROBINSON_PlusPlus.Meta.Representability2Prf.prf_ancla (prf_listFormCodeM_numeral axioms)
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_not_In_numeral h) _)
    (PrfH_eq_subst_in (prf_to_prfH hA _) (prfH_hyp_self _))

/-- La conclusión de una línea, comparada en ℕ con la reconstrucción evaluada. -/
theorem dec_concl {x : Nat} (hx : x ≠ 0) {R : Term} {r : Nat} (hR : Prf (R =eq numeralM r)) :
    Or (carN x = r) (Prf ((carc (numeralM x) =eq R) ⇒ Formula.bottom)) := by
  by_cases h : carN x = r
  · exact Or.inl h
  · refine Or.inr (prf_deduction ?_)
    exact PrfH.mp _ _ _ (prf_to_prfH (crit_num_ne (carN x) r h) _)
      (PrfH_eq_trans (PrfH_eq_trans (prf_to_prfH (prf_eq_symm (prf_carc_numeral hx)) _) (prfH_hyp_self _))
        (prf_to_prfH hR _))

/-- La guarda de fórmula de una casilla, decidida (GuardNeg). -/
theorem dec_hasWitF {A : Term} {a : Nat} (hA : Prf (A =eq numeralM a)) :
    Or (hasWitFN a) (Prf (hasWitF A ⇒ Formula.bottom)) := by
  rcases hasWitF_decide a with h | h
  · exact Or.inl h
  · exact Or.inr (prf_deduction (PrfH.mp _ _ _ (prf_to_prfH h _)
      (ROBINSON_PlusPlus.Meta.SubstfcWitnessPrf.PrfH_congr_hasWitF (prf_to_prfH hA _) (prfH_hyp_self _))))

/-- La de término. -/
theorem dec_hasWit {T : Term} {t : Nat} (hT : Prf (T =eq numeralM t)) :
    Or (hasWitN t) (Prf (hasWit T ⇒ Formula.bottom)) := by
  rcases hasWit_decide t with h | h
  · exact Or.inl h
  · exact Or.inr (prf_deduction (PrfH.mp _ _ _ (prf_to_prfH h _)
      (ROBINSON_PlusPlus.Meta.HasWitTcFnPrf.PrfH_congr_hasWit (prf_to_prfH hT _) (prfH_hyp_self _))))

/-! ## §4 · Una rama de la inversión -/

/-- La rama `k`: con la etiqueta `k`, `lineWF x̄` es absurda. -/
def Rama (x k : Nat) : Formula :=
  (nthc (numeralM x) (succ zero) =eq numeralM k) ⇒ (lineWF (numeralM x) ⇒ Formula.bottom)

/-- Cae por la longitud. -/
theorem branch_len {x k ℓ : Nat} {R : Formula}
    (hax : Prf ((nthc (numeralM x) (succ zero) =eq numeralM k) ⇒
      (lineWF (numeralM x) ⇒ Formula.and (lenc (numeralM x) =eq numeralM ℓ) R)))
    (hl : ¬ lenN x = ℓ) : Prf (Rama x k) :=
  imp2_post hax (rejL (crit_len_absurd _ (lenN x) ℓ hl (prf_lenc_numeral x)))

/-- Cae por su RHS. -/
theorem branch_R {x k ℓ : Nat} {R : Formula}
    (hax : Prf ((nthc (numeralM x) (succ zero) =eq numeralM k) ⇒
      (lineWF (numeralM x) ⇒ Formula.and (lenc (numeralM x) =eq numeralM ℓ) R)))
    (hR : Prf (R ⇒ Formula.bottom)) : Prf (Rama x k) :=
  imp2_post hax (rejR hR)

/-- Cae por la etiqueta, si se puede leer. -/
theorem tag_absurd {x k : Nat} (h1 : 1 < lenN x) (hk : ¬ nthN x 1 = k) : Prf (Rama x k) :=
  impT (crit_nth_absurd (numeralM x) 1 (nthN x 1) k hk (prf_nthc_numeral 1 x h1)) (Prf.incl (Prfᵢ.efq _))

/-- Una rama de otra etiqueta cae: por la etiqueta si la longitud es la de su regla (`ℓ ≥ 2`), o por la longitud. -/
theorem branch_tag {x k ℓ : Nat} {R : Formula} (hℓ : 2 ≤ ℓ)
    (hax : Prf ((nthc (numeralM x) (succ zero) =eq numeralM k) ⇒
      (lineWF (numeralM x) ⇒ Formula.and (lenc (numeralM x) =eq numeralM ℓ) R)))
    (hk : ¬ nthN x 1 = k) : Prf (Rama x k) := by
  by_cases hl : lenN x = ℓ
  · exact tag_absurd (by rw [hl]; exact hℓ) hk
  · exact branch_len hax hl

/-- La rama de la etiqueta propia, decidida: la regla se cumple en ℕ, o la rama cae. -/
theorem refT_of {x k ℓ : Nat} {R : Formula} {P : Prop}
    (hax : Prf ((nthc (numeralM x) (succ zero) =eq numeralM k) ⇒
      (lineWF (numeralM x) ⇒ Formula.and (lenc (numeralM x) =eq numeralM ℓ) R)))
    (hR : lenN x = ℓ → Or P (Prf (R ⇒ Formula.bottom))) : Or (And (lenN x = ℓ) P) (Prf (Rama x k)) := by
  by_cases hl : lenN x = ℓ
  · rcases hR hl with hp | hr
    · exact Or.inl ⟨hl, hp⟩
    · exact Or.inr (branch_R hax hr)
  · exact Or.inr (branch_len hax hl)

/-! ## §5 · Las 21 reglas -/

theorem refT_p1 (x : Nat) : Or (lineWFT Vax 0 x) (Prf (Rama x 0)) :=
  refT_of (axL_p1 (numeralM x)) fun hl => dec_concl (nz hl) (evImpl (hN hl 2) (evImpl (hN hl 3) (hN hl 2)))

theorem refT_p2 (x : Nat) : Or (lineWFT Vax 1 x) (Prf (Rama x 1)) :=
  refT_of (axL_p2 (numeralM x)) fun hl => dec_concl (nz hl)
    (evImpl (evImpl (hN hl 2) (evImpl (hN hl 3) (hN hl 4))) (evImpl (evImpl (hN hl 2) (hN hl 3)) (evImpl (hN hl 2) (hN hl 4))))

theorem refT_c1 (x : Nat) : Or (lineWFT Vax 2 x) (Prf (Rama x 2)) :=
  refT_of (axL_c1 (numeralM x)) fun hl => dec_concl (nz hl)
    (evImpl (hN hl 2) (evImpl (hN hl 3) (evAnd (hN hl 2) (hN hl 3))))

theorem refT_c2 (x : Nat) : Or (lineWFT Vax 3 x) (Prf (Rama x 3)) :=
  refT_of (axL_c2 (numeralM x)) fun hl => dec_concl (nz hl) (evImpl (evAnd (hN hl 2) (hN hl 3)) (hN hl 2))

theorem refT_c3 (x : Nat) : Or (lineWFT Vax 4 x) (Prf (Rama x 4)) :=
  refT_of (axL_c3 (numeralM x)) fun hl => dec_concl (nz hl) (evImpl (evAnd (hN hl 2) (hN hl 3)) (hN hl 3))

theorem refT_j1 (x : Nat) : Or (lineWFT Vax 5 x) (Prf (Rama x 5)) :=
  refT_of (axL_j1 (numeralM x)) fun hl => dec_concl (nz hl) (evImpl (hN hl 2) (evOr (hN hl 2) (hN hl 3)))

theorem refT_j2 (x : Nat) : Or (lineWFT Vax 6 x) (Prf (Rama x 6)) :=
  refT_of (axL_j2 (numeralM x)) fun hl => dec_concl (nz hl) (evImpl (hN hl 3) (evOr (hN hl 2) (hN hl 3)))

theorem refT_j3 (x : Nat) : Or (lineWFT Vax 7 x) (Prf (Rama x 7)) :=
  refT_of (axL_j3 (numeralM x)) fun hl => dec_concl (nz hl)
    (evImpl (evOr (hN hl 2) (hN hl 3)) (evImpl (evImpl (hN hl 2) (hN hl 4)) (evImpl (evImpl (hN hl 3) (hN hl 4)) (hN hl 4))))

theorem refT_efq (x : Nat) : Or (lineWFT Vax 8 x) (Prf (Rama x 8)) :=
  refT_of (axL_efq (numeralM x)) fun hl => dec_concl (nz hl) (evImpl prf_botc_numeral (hN hl 2))

theorem refT_q1 (x : Nat) : Or (lineWFT Vax 9 x) (Prf (Rama x 9)) :=
  refT_of (axL_q1 (numeralM x)) fun hl => by
    rcases dec_hasWitF (hN hl 2) with hF | hF
    · rcases dec_hasWit (hN hl 3) with hT | hT
      · rcases dec_concl (nz hl) (evImpl (evAll (hN hl 2))
            (evSubst 0 (hN hl 3) (hN hl 2) (codF_of_hasWitFN hF) (codT_of_hasWitN hT))) with he | he
        · exact Or.inl ⟨hF, hT, he⟩
        · exact Or.inr (rejR (rejR he))
      · exact Or.inr (rejR (rejL hT))
    · exact Or.inr (rejL hF)

theorem refT_q2 (x : Nat) : Or (lineWFT Vax 10 x) (Prf (Rama x 10)) :=
  refT_of (axL_q2 (numeralM x)) fun hl => by
    rcases dec_hasWitF (hN hl 2) with hF | hF
    · rcases dec_hasWit (hN hl 3) with hT | hT
      · rcases dec_concl (nz hl) (evImpl (evSubst 0 (hN hl 3) (hN hl 2) (codF_of_hasWitFN hF) (codT_of_hasWitN hT))
            (evExc (hN hl 2))) with he | he
        · exact Or.inl ⟨hF, hT, he⟩
        · exact Or.inr (rejR (rejR he))
      · exact Or.inr (rejR (rejL hT))
    · exact Or.inr (rejL hF)

theorem refT_q3 (x : Nat) : Or (lineWFT Vax 11 x) (Prf (Rama x 11)) :=
  refT_of (axL_q3 (numeralM x)) fun hl => by
    rcases dec_hasWitF (hN hl 3) with hF | hF
    · rcases dec_concl (nz hl) (evImpl (evAll (evImpl (hN hl 2) (evLift 0 (hN hl 3) (codF_of_hasWitFN hF))))
          (evImpl (evExc (hN hl 2)) (hN hl 3))) with he | he
      · exact Or.inl ⟨hF, he⟩
      · exact Or.inr (rejR he)
    · exact Or.inr (rejL hF)

theorem refT_eqrefl (x : Nat) : Or (lineWFT Vax 12 x) (Prf (Rama x 12)) :=
  refT_of (axL_eqrefl (numeralM x)) fun hl => dec_concl (nz hl) (evEqc (hN hl 2) (hN hl 2))

theorem refT_leibniz (x : Nat) : Or (lineWFT Vax 13 x) (Prf (Rama x 13)) :=
  refT_of (axL_leibniz (numeralM x)) fun hl => by
    rcases dec_hasWitF (hN hl 2) with hF | hF
    · rcases dec_hasWit (hN hl 3) with hT | hT
      · rcases dec_hasWit (hN hl 4) with hT' | hT'
        · rcases dec_concl (nz hl) (evImpl (evEqc (hN hl 3) (hN hl 4))
              (evImpl (evSubst 0 (hN hl 3) (hN hl 2) (codF_of_hasWitFN hF) (codT_of_hasWitN hT))
                (evSubst 0 (hN hl 4) (hN hl 2) (codF_of_hasWitFN hF) (codT_of_hasWitN hT')))) with he | he
          · exact Or.inl ⟨hF, hT, hT', he⟩
          · exact Or.inr (rejR (rejR (rejR he)))
        · exact Or.inr (rejR (rejR (rejL hT')))
      · exact Or.inr (rejR (rejL hT))
    · exact Or.inr (rejL hF)

theorem refT_p3 (x : Nat) : Or (lineWFT Vax 14 x) (Prf (Rama x 14)) :=
  refT_of (axL_p3 (numeralM x)) fun hl => dec_concl (nz hl)
    (evImpl (evImpl (evImpl (hN hl 2) prf_botc_numeral) prf_botc_numeral) (hN hl 2))

theorem refT_thy (x : Nat) : Or (lineWFT Vax 15 x) (Prf (Rama x 15)) :=
  refT_of (axL_thy (numeralM x)) fun hl => by
    by_cases hm : memN (carN x) Vax
    · exact Or.inl hm
    · exact Or.inr (prf_deduction (PrfH.mp _ _ _ (prf_to_prfH (prf_not_In_axiomsCodeT hm) _)
        (PrfH_congr_In_left (prf_to_prfH (prf_carc_numeral (nz hl)) _) (prfH_hyp_self _))))

theorem refT_mp (x : Nat) : Or (lineWFT Vax 16 x) (Prf (Rama x 16)) := by
  by_cases hl : lenN x = 3
  · exact Or.inl hl
  · exact Or.inr (imp2_post (axL_mp (numeralM x)) (crit_len_absurd _ (lenN x) 3 hl (prf_lenc_numeral x)))

theorem refT_gen (x : Nat) : Or (lineWFT Vax 17 x) (Prf (Rama x 17)) :=
  refT_of (axL_gen (numeralM x)) fun hl => dec_concl (nz hl) (evAll (hN hl 2))

theorem refT_ind (x : Nat) : Or (lineWFT Vax 18 x) (Prf (Rama x 18)) :=
  refT_of (axL_ind (numeralM x)) fun hl => by
    rcases dec_hasWitF (hN hl 2) with hF | hF
    · have hc := codF_of_hasWitFN hF
      rcases dec_concl (nz hl) (evImpl (evSubst 0 (evTC zero) (hN hl 2) hc codT_TC0)
          (evImpl (evAll (evImpl (hN hl 2) (evSubst 0 (evTC (succ (.var 0))) (evLift 1 (hN hl 2) hc)
            (codF_liftfcN hc 1) codT_TCS))) (evAll (hN hl 2)))) with he | he
      · exact Or.inl ⟨hF, he⟩
      · exact Or.inr (rejR he)
    · exact Or.inr (rejL hF)

theorem refT_qconf (x : Nat) : Or (lineWFT Vax 19 x) (Prf (Rama x 19)) :=
  refT_of (axL_qconf (numeralM x)) fun hl => by
    rcases dec_hasWitF (hN hl 2) with hF | hF
    · rcases dec_concl (nz hl) (evImpl (evAll (evImpl (evLift 0 (hN hl 2) (codF_of_hasWitFN hF)) (hN hl 3)))
          (evImpl (hN hl 2) (evAll (hN hl 3)))) with he | he
      · exact Or.inl ⟨hF, he⟩
      · exact Or.inr (rejR he)
    · exact Or.inr (rejL hF)

theorem refT_listInd (x : Nat) : Or (lineWFT Vax 20 x) (Prf (Rama x 20)) :=
  refT_of (axL_listInd (numeralM x)) fun hl => by
    rcases dec_hasWitF (hN hl 2) with hF | hF
    · have hc := codF_of_hasWitFN hF
      rcases dec_concl (nz hl) (evImpl (evSubst 0 (evTC nil) (hN hl 2) hc codT_TNIL)
          (evImpl (evAll (evAll (evImpl (evLift 1 (hN hl 2) hc)
            (evSubst 0 (evTC (cons (.var 1) (.var 0))) (evLift 2 (evLift 1 (hN hl 2) hc) (codF_liftfcN hc 1))
              (codF_liftfcN (codF_liftfcN hc 1) 2) codT_TCONS)))) (evAll (hN hl 2)))) with he | he
      · exact Or.inl ⟨hF, he⟩
      · exact Or.inr (rejR he)
    · exact Or.inr (rejL hF)

/-! ## §6 · El ensamblaje por la inversión -/

theorem gt20 (n : Nat) : ¬ (n + 21 < 21) :=
  Nat.not_lt_of_le (Nat.le_add_left 21 n)

/-- La rama de la etiqueta propia, para las 21. -/
theorem refT (x : Nat) : ∀ k : Nat, k < 21 → Or (lineWFT Vax k x) (Prf (Rama x k))
  | 0, _ => refT_p1 x
  | 1, _ => refT_p2 x
  | 2, _ => refT_c1 x
  | 3, _ => refT_c2 x
  | 4, _ => refT_c3 x
  | 5, _ => refT_j1 x
  | 6, _ => refT_j2 x
  | 7, _ => refT_j3 x
  | 8, _ => refT_efq x
  | 9, _ => refT_q1 x
  | 10, _ => refT_q2 x
  | 11, _ => refT_q3 x
  | 12, _ => refT_eqrefl x
  | 13, _ => refT_leibniz x
  | 14, _ => refT_p3 x
  | 15, _ => refT_thy x
  | 16, _ => refT_mp x
  | 17, _ => refT_gen x
  | 18, _ => refT_ind x
  | 19, _ => refT_qconf x
  | 20, _ => refT_listInd x
  | n + 21, h => absurd h (gt20 n)

theorem mism_mp {x : Nat} (hk : ¬ nthN x 1 = 16) : Prf (Rama x 16) := by
  by_cases hl : lenN x = 3
  · exact tag_absurd (by rw [hl]; decide) hk
  · exact imp2_post (axL_mp (numeralM x)) (crit_len_absurd _ (lenN x) 3 hl (prf_lenc_numeral x))

/-- Las ramas de otra etiqueta, para las 21. -/
theorem mism (x : Nat) : ∀ k : Nat, k < 21 → ¬ nthN x 1 = k → Prf (Rama x k)
  | 0, _, h => branch_tag (by decide) (axL_p1 (numeralM x)) h
  | 1, _, h => branch_tag (by decide) (axL_p2 (numeralM x)) h
  | 2, _, h => branch_tag (by decide) (axL_c1 (numeralM x)) h
  | 3, _, h => branch_tag (by decide) (axL_c2 (numeralM x)) h
  | 4, _, h => branch_tag (by decide) (axL_c3 (numeralM x)) h
  | 5, _, h => branch_tag (by decide) (axL_j1 (numeralM x)) h
  | 6, _, h => branch_tag (by decide) (axL_j2 (numeralM x)) h
  | 7, _, h => branch_tag (by decide) (axL_j3 (numeralM x)) h
  | 8, _, h => branch_tag (by decide) (axL_efq (numeralM x)) h
  | 9, _, h => branch_tag (by decide) (axL_q1 (numeralM x)) h
  | 10, _, h => branch_tag (by decide) (axL_q2 (numeralM x)) h
  | 11, _, h => branch_tag (by decide) (axL_q3 (numeralM x)) h
  | 12, _, h => branch_tag (by decide) (axL_eqrefl (numeralM x)) h
  | 13, _, h => branch_tag (by decide) (axL_leibniz (numeralM x)) h
  | 14, _, h => branch_tag (by decide) (axL_p3 (numeralM x)) h
  | 15, _, h => branch_tag (by decide) (axL_thy (numeralM x)) h
  | 16, _, h => mism_mp h
  | 17, _, h => branch_tag (by decide) (axL_gen (numeralM x)) h
  | 18, _, h => branch_tag (by decide) (axL_ind (numeralM x)) h
  | 19, _, h => branch_tag (by decide) (axL_qconf (numeralM x)) h
  | 20, _, h => branch_tag (by decide) (axL_listInd (numeralM x)) h
  | n + 21, h, _ => absurd h (gt20 n)

/-- La disyunción de la inversión, eliminada rama a rama. -/
theorem tagDisj_elim (X : Term) (C : Formula) :
    ∀ n : Nat, (∀ k, k < n + 1 → Prf ((lineTag X =eq numeralM k) ⇒ C)) → Prf (tagDisj X n ⇒ C)
  | 0, h => h 0 (Nat.succ_pos 0)
  | n + 1, h => prf_or_elim_imp (h (n + 1) (Nat.lt_succ_self _))
      (tagDisj_elim X C n fun k hk => h k (Nat.lt_succ_of_lt hk))

/-- Si las 21 ramas caen, `lineWF x̄` cae: por `ax_lineWF_inv`. -/
theorem assemble (x : Nat) (hb : ∀ k, k < 21 → Prf (Rama x k)) : Prf (neg (lineWF (numeralM x))) := by
  have hd := tagDisj_elim (numeralM x) (lineWF (numeralM x) ⇒ Formula.bottom) 20 hb
  refine prf_deduction ?_
  have hl := prfH_hyp_self (lineWF (numeralM x))
  have ht := PrfH.mp _ _ _ (prf_to_prfH (ROBINSON_PlusPlus.Meta.Sigma1AtomPrf.prf_lineWF_inv _) _) hl
  exact PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH hd _) ht) hl

/-- 🏁 **La buena formación de una línea, DECIDIDA**: la línea es buena en ℕ, o `Prf` la refuta. -/
theorem lineWF_decide (x : Nat) : Or (lineWFN Vax x) (Prf (neg (lineWF (numeralM x)))) := by
  by_cases hk : nthN x 1 < 21
  · rcases refT x (nthN x 1) hk with hT | hR
    · exact Or.inl ⟨hk, hT⟩
    · refine Or.inr (assemble x fun k hk20 => ?_)
      by_cases e : nthN x 1 = k
      · rw [← e]; exact hR
      · exact mism x k hk20 e
  · exact Or.inr (assemble x fun k hk20 => mism x k hk20 fun e => hk (by rw [e]; exact hk20))

/-- 🏁 **NegLineWF**: si la línea no es buena en ℕ, `Prf` refuta `lineWF x̄`. -/
theorem prf_neg_lineWF {x : Nat} (h : ¬ lineWFN Vax x) : Prf (neg (lineWF (numeralM x))) := by
  rcases lineWF_decide x with hl | hr
  · exact absurd hl h
  · exact hr

/-! ## §7 · Controles -/

/-- ✅ La hipótesis se cumple: el `0` no es una línea, y `Prf` lo refuta. -/
theorem control_neg_lineWF_zero : Prf (neg (lineWF (numeralM 0))) :=
  prf_neg_lineWF (x := 0) fun ⟨_, h⟩ => by
    rw [nthN_zero_l] at h
    exact absurd h.1 (by rw [lenN_zero]; decide)

/-- ✅ **…y sólo donde la línea es mala**: donde es buena en ℕ, `Prf` no la refuta, por la solidez en `MNV V₀`.
    Nombra la semántica: es el control positivo del `#pureza`. -/
theorem control_exacta (x : Nat) (h : lineWFN Vax x) : ¬ Prf (neg (lineWF (numeralM x))) := by
  intro hp
  have hs := ROBINSON_PlusPlus.Meta.SolidezPrf.prf_sound ROBINSON_PlusPlus.Meta.Consistencia.estandar_MN hp
    (fun _ => 0)
  apply hs
  have e := ROBINSON_PlusPlus.Meta.ModeloEstandar.ev_numeralM (V := codeNatList axioms) (fun _ => 0) x
  simp only [lineWF, FOL.Metamath.Semantics.evalFormula, FOL.Metamath.Semantics.evalTerms, e,
    ROBINSON_PlusPlus.Meta.ModeloEstandar.MN_lineWF, ROBINSON_PlusPlus.Meta.Consistencia.V₀_eq_codigo]
  exact h

end ROBINSON_PlusPlus.Meta.RosserNegLinea

#print axioms ROBINSON_PlusPlus.Meta.RosserNegLinea.lineWF_decide
#print axioms ROBINSON_PlusPlus.Meta.RosserNegLinea.prf_neg_lineWF
#print axioms ROBINSON_PlusPlus.Meta.RosserNegLinea.prf_not_In_axiomsCodeT
#print axioms ROBINSON_PlusPlus.Meta.RosserNegLinea.refT_q1
#print axioms ROBINSON_PlusPlus.Meta.RosserNegLinea.refT_thy
#print axioms ROBINSON_PlusPlus.Meta.RosserNegLinea.refT_ind

/-! T08 en el módulo (ADR‑147): lo de esta etapa no nombra la semántica; `control_exacta`, que usa la solidez en el
    modelo, sí. -/
#pureza ROBINSON_PlusPlus.Meta.RosserNegLinea.lineWF_decide ROBINSON_PlusPlus.Meta.RosserNegLinea.prf_neg_lineWF
  ROBINSON_PlusPlus.Meta.RosserNegLinea.prf_not_In_axiomsCodeT ROBINSON_PlusPlus.Meta.RosserNegLinea.refT
  ROBINSON_PlusPlus.Meta.RosserNegLinea.mism ROBINSON_PlusPlus.Meta.RosserNegLinea.control_neg_lineWF_zero
  | ROBINSON_PlusPlus.Meta.RosserNegLinea.control_exacta

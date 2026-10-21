/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.RosserNegLinea
import ROBINSON_PlusPlus.Meta.RosserW1
import ROBINSON_PlusPlus.Meta.RosserPosNum
import ROBINSON_PlusPlus.Meta.PremsOfTagPrf

/-!
# `Meta/RosserNegNum.lean` — Rosser, etapa 5: NegNum, lo que no es una prueba se refuta (ADR‑146 §3, ADR‑147, ADR‑156)

**Qué.** El predicado de prueba de T sobre numerales, decidido, con `PfF y x = chainOk nil y ∧ In x (runFn nil y)`
(ADR‑149) y su espejo en ℕ `ProofN` (ADR‑148):

    proofN_decide m y : ProofN m y ∨ Prf (¬ PfF m̄ ȳ)
    negNum            : ¬ ProofN m y → Prf (¬ PfF m̄ ȳ)
    negNum'           : ¬ Prf (dec y) → ∀ m, Prf (¬ PfF m̄ ȳ)          -- con W1(ax)

* **§1** ℕ: las líneas de una cadena buena no son `0`, y la inclusión de las premisas, decidida (`allInN_dec`).
* **§2** `Prf`: las premisas sobre numerales. Sólo `mp` y `gen` tienen (`premsOfN` es `0` en las otras 19); su
  `premsOf` lo evalúan `prf_premsOf_mp`/`prf_premsOf_gen` (`Meta/PremsOfTagPrf.lean`) y la cola del numeral. Una premisa
  que falta en el acumulador refuta la línea (`prf_neg_lineOk_prem`).
* **§3** La cadena, decidida línea a línea (`chainOk_decide`): la línea mala, por NegLineWF (ADR‑154); la premisa que
  falta, por §2; y la buena, con el acumulador evaluado (`concat`, ADR‑150), por la hipótesis de inducción.
* **§4** NegNum, y NegNum′ con W1(ax): si `dec y` no es teorema, T refuta cada candidata a prueba de `y`
  (`negNum'`, `negNum_formula`, `negNum_formCode`: la forma de `posNum`).

**Controles** (los de ADR‑146 §4): la hipótesis de `negNum` puede valer, la cadena vacía (`control_negNum_vacia`), y
puede fallar, la prueba de un axioma (`control_falla`, con `proofN_axioma`); `control_exacta`, por la solidez en
`MNV V₀`: donde `ProofN` vale, `Prf` no refuta `PfF`. Los dos últimos nombran la semántica: son el control positivo del
`#pureza`.

⛔ Ningún numeral se evalúa: las cadenas se recorren por `encodeL`/`decodeL` con lemas ∀.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open FOL ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Hilbert ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ChainPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs
open ROBINSON_PlusPlus.Meta.ModeloCodigo ROBINSON_PlusPlus.Meta.RosserNumerales ROBINSON_PlusPlus.Meta.RosserNumEval
open ROBINSON_PlusPlus.Meta.RosserGuardNeg ROBINSON_PlusPlus.Meta.RosserNegLinea
open ROBINSON_PlusPlus.Meta.RosserW1 ROBINSON_PlusPlus.Meta.RosserPosNum ROBINSON_PlusPlus.Meta.SolidezVerificador

namespace ROBINSON_PlusPlus.Meta.RosserNegNum

/-! ## §1 · ℕ: las líneas de una cadena buena, y las premisas -/

/-- Una línea buena no es `0` (su longitud es la de su regla, ≥ 2). -/
theorem lineWFN_ne_zero {V x : Nat} (h : lineWFN V x) : x ≠ 0 := by
  rintro rfl
  obtain ⟨_, h2⟩ := h
  rw [nthN_zero_l] at h2
  exact absurd h2.1 (by rw [lenN_zero]; decide)

theorem chainOkL_line : ∀ (L : List Nat) (c : Nat), chainOkL Vax c L → ∀ x, List.Mem x L → lineWFN Vax x
  | [], _, _, _, hx => nomatch hx
  | _ :: _, _, h, _, List.Mem.head _ => h.1.1
  | _ :: r, _, h, x, List.Mem.tail _ hx => chainOkL_line r _ h.2 x hx

/-- Las líneas de una cadena buena no son `0`: lo que pide `prf_not_In_runFn`. -/
theorem lines_ne_zero {c m : Nat} (h : chainOkN Vax c m) : ∀ x, memN x m → x ≠ 0 :=
  fun x hx => lineWFN_ne_zero (chainOkL_line (decodeL m) c h x hx)

theorem allInN_dec_encodeL (c : Nat) :
    ∀ L : List Nat, Or (allInN c (encodeL L)) (∃ y, And (List.Mem y L) (¬ memN y c))
  | [] => Or.inl (allInN_zero c)
  | a :: L => by
      by_cases ha : memN a c
      · rcases allInN_dec_encodeL c L with h | ⟨y, hy, hn⟩
        · exact Or.inl ((allInN_consN c a (encodeL L)).mpr ⟨ha, h⟩)
        · exact Or.inr ⟨y, List.Mem.tail a hy, hn⟩
      · exact Or.inr ⟨a, List.Mem.head L, ha⟩

/-- La inclusión de las premisas, decidida (sin lógica clásica: `decMemN`). -/
theorem allInN_dec (c P : Nat) : Or (allInN c P) (∃ y, And (memN y P) (¬ memN y c)) := by
  have h := allInN_dec_encodeL c (decodeL P)
  rw [encodeL_decodeL] at h
  exact h

/-! ## §2 · `Prf`: las premisas sobre numerales -/

/-- De `allIn c̄ L̄`, cada elemento de la lista está en `c̄`. -/
theorem prf_allIn_In_encodeL (c y : Nat) : ∀ L : List Nat, List.Mem y L →
    Prf (allIn (numeralM c) (numeralM (encodeL L)) ⇒ In (numeralM y) (numeralM c))
  | _ :: L, List.Mem.head _ => by
      refine prf_deduction ?_
      have h1 := PrfH_allIn_subst2 (prf_to_prfH (prf_eq_symm (prf_cons_evalM y (encodeL L))) _)
        (prfH_hyp_self (allIn (numeralM c) (numeralM (encodeL (y :: L)))))
      exact PrfH_and_elim_left (PrfH_iff_mp (prf_allIn_cons _ _ _) h1)
  | a :: L, List.Mem.tail _ hm => by
      refine prf_deduction ?_
      have h1 := PrfH_allIn_subst2 (prf_to_prfH (prf_eq_symm (prf_cons_evalM a (encodeL L))) _)
        (prfH_hyp_self (allIn (numeralM c) (numeralM (encodeL (a :: L)))))
      exact PrfH.mp _ _ _ (prf_to_prfH (prf_allIn_In_encodeL c y L hm) _)
        (PrfH_and_elim_right (PrfH_iff_mp (prf_allIn_cons _ _ _) h1))

theorem prf_allIn_In_numeral {c P y : Nat} (hy : memN y P) :
    Prf (allIn (numeralM c) (numeralM P) ⇒ In (numeralM y) (numeralM c)) := by
  have e := prf_allIn_In_encodeL c y (decodeL P) hy
  rw [encodeL_decodeL] at e
  exact e

/-- La casilla 2 de una línea de longitud 3, por la cola: `carc (cdrc (cdrc x̄)) = ⟨nthN x 2⟩‾`. -/
theorem prf_ccc {x : Nat} (hl : lenN x = 3) :
    Prf (carc (cdrc (cdrc (numeralM x))) =eq numeralM (nthN x 2)) := by
  have h0 : x ≠ 0 := nz hl
  have hl1 : lenN (cdrN x) = 2 := by
    have e := lenN_cdrN h0; rw [hl] at e; exact (Nat.succ.inj e).symm
  have h1 : cdrN x ≠ 0 := ne_zero_of_lenN hl1 (by decide)
  have hl2 : lenN (cdrN (cdrN x)) = 1 := by
    have e := lenN_cdrN h1; rw [hl1] at e; exact (Nat.succ.inj e).symm
  have h2 : cdrN (cdrN x) ≠ 0 := ne_zero_of_lenN hl2 (by decide)
  exact prf_eq_trans (prf_congr_carc (prf_eq_trans (prf_congr_cdrc (prf_cdrc_numeral h0)) (prf_cdrc_numeral h1)))
    (prf_carc_numeral h2)

/-- La etiqueta de una línea de longitud ≥ 2, evaluada. -/
theorem prf_tag {x k : Nat} (h1 : 1 < lenN x) (hk : nthN x 1 = k) :
    Prf (nthc (numeralM x) (succ zero) =eq numeralM k) := by
  have h := prf_nthc_numeral 1 x h1
  rw [hk] at h
  exact h

/-- `premsOf` de una línea `mp`, sobre el numeral. -/
theorem prf_premsOf_mp_num {x : Nat} (hl : lenN x = 3) (hk : nthN x 1 = 16) :
    Prf (lineWF (numeralM x) ⇒ (premsOf (numeralM x) =eq numeralM (premsOfN x))) := by
  have hP : premsOfN x = consN (implcN (nthN x 2) (carN x)) (consN (nthN x 2) 0) := by
    rw [premsOfN, ite_eq_left hk]
    rfl
  rw [hP]
  refine prf_deduction ?_
  have h1 := PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (PremsOfTagPrf.prf_premsOf_mp (numeralM x)) _)
    (prfH_hyp_self _)) (prf_to_prfH (prf_tag (by rw [hl]; decide) hk) _)
  exact PrfH_eq_trans h1 (prf_to_prfH (prf_cons_evalM_of (evImpl (prf_ccc hl) (prf_carc_numeral (nz hl)))
    (prf_cons_evalM_of (prf_ccc hl) (prf_refl (numeralM 0)))) _)

/-- `premsOf` de una línea `gen`, sobre el numeral. -/
theorem prf_premsOf_gen_num {x : Nat} (hl : lenN x = 3) (hk : nthN x 1 = 17) :
    Prf (lineWF (numeralM x) ⇒ (premsOf (numeralM x) =eq numeralM (premsOfN x))) := by
  have hP : premsOfN x = consN (nthN x 2) 0 := by
    rw [premsOfN, ite_eq_right (by rw [hk]; decide), ite_eq_left hk]
  rw [hP]
  refine prf_deduction ?_
  have h1 := PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (PremsOfTagPrf.prf_premsOf_gen (numeralM x)) _)
    (prfH_hyp_self _)) (prf_to_prfH (prf_tag (by rw [hl]; decide) hk) _)
  exact PrfH_eq_trans h1 (prf_to_prfH (prf_cons_evalM_of (prf_ccc hl) (prf_refl (numeralM 0))) _)

/-- 🏁 **Una premisa que falta en el acumulador refuta la línea.** -/
theorem prf_neg_lineOk_prem {c x y : Nat} (hw : lineWFN Vax x) (hy : memN y (premsOfN x)) (hn : ¬ memN y c) :
    Prf (lineOk (numeralM c) (numeralM x) ⇒ Formula.bottom) := by
  have key : Prf (lineWF (numeralM x) ⇒ (premsOf (numeralM x) =eq numeralM (premsOfN x))) := by
    by_cases h16 : nthN x 1 = 16
    · exact prf_premsOf_mp_num ((lineWFN_of_tag h16 (by decide)).mp hw) h16
    · by_cases h17 : nthN x 1 = 17
      · exact prf_premsOf_gen_num ((lineWFN_of_tag h17 (by decide)).mp hw).1 h17
      · have hP : premsOfN x = 0 := by rw [premsOfN, ite_eq_right h16, ite_eq_right h17]
        rw [hP] at hy
        exact absurd hy (memN_zero y)
  refine prf_deduction ?_
  have hh := prfH_hyp_self (lineOk (numeralM c) (numeralM x))
  have hal := PrfH_allIn_subst2 (PrfH.mp _ _ _ (prf_to_prfH key _) (PrfH_and_elim_left hh)) (PrfH_and_elim_right hh)
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_not_In_numeral hn) _)
    (PrfH.mp _ _ _ (prf_to_prfH (prf_allIn_In_numeral hy) _) hal)

/-! ## §3 · La cadena, decidida línea a línea -/

/-- Refutar la cabeza o la cola de una cadena no vacía la refuta. -/
theorem prf_neg_chainOk_cons {c x : Nat} {r : List Nat}
    (h : Prf (land (lineOk (numeralM c) (numeralM x))
      (chainOk (concat (numeralM c) (cons (carc (numeralM x)) nil)) (numeralM (encodeL r))) ⇒ Formula.bottom)) :
    Prf (neg (chainOk (numeralM c) (numeralM (encodeL (x :: r))))) := by
  refine prf_deduction ?_
  have h1 := PrfH_chainOk_subst2 (prf_to_prfH (prf_eq_symm (prf_cons_evalM x (encodeL r))) _)
    (prfH_hyp_self (chainOk (numeralM c) (numeralM (encodeL (x :: r)))))
  exact PrfH.mp _ _ _ (prf_to_prfH h _) (PrfH_iff_mp (prf_chainOk_cons _ _ _) h1)

/-- 🏁 **La cadena, DECIDIDA**: buena en ℕ, o `Prf` la refuta. -/
theorem chainOk_decide : ∀ (L : List Nat) (c : Nat),
    Or (chainOkL Vax c L) (Prf (neg (chainOk (numeralM c) (numeralM (encodeL L)))))
  | [], _ => Or.inl trivial
  | x :: r, c => by
      rcases lineWF_decide x with hw | hw
      · rcases allInN_dec c (premsOfN x) with ha | ⟨y, hy, hn⟩
        · rcases chainOk_decide r (concatN c (consN (carN x) 0)) with hr | hr
          · exact Or.inl ⟨⟨hw, ha⟩, hr⟩
          · have hacc : Prf (concat (numeralM c) (cons (carc (numeralM x)) nil) =eq
                numeralM (concatN c (consN (carN x) 0))) :=
              prf_eq_trans (prf_congr_concat_left
                (prf_cons_evalM_of (prf_carc_numeral (lineWFN_ne_zero hw)) (prf_refl (numeralM 0))))
                (prf_concat_numeral c (consN (carN x) 0))
            exact Or.inr (prf_neg_chainOk_cons (rejR (prf_deduction (PrfH.mp _ _ _ (prf_to_prfH hr _)
              (PrfH_chainOk_subst1 (prf_to_prfH hacc _) (prfH_hyp_self _))))))
        · exact Or.inr (prf_neg_chainOk_cons (rejL (prf_neg_lineOk_prem hw hy hn)))
      · exact Or.inr (prf_neg_chainOk_cons (rejL (rejL hw)))

theorem chainOkN_decide (c m : Nat) : Or (chainOkN Vax c m) (Prf (neg (chainOk (numeralM c) (numeralM m)))) := by
  have h := chainOk_decide (decodeL m) c
  rw [encodeL_decodeL] at h
  exact h

/-! ## §4 · NegNum -/

/-- 🏁 **El predicado de prueba de T, DECIDIDO** sobre numerales. -/
theorem proofN_decide (m y : Nat) : Or (ProofN m y) (Prf (neg (PfF (numeralM m) (numeralM y)))) := by
  rcases chainOkN_decide 0 m with hc | hc
  · by_cases hy : memN y (runFnN 0 m)
    · exact Or.inl ⟨hc, hy⟩
    · exact Or.inr (rejR (prf_not_In_runFn (lines_ne_zero hc) hy))
  · exact Or.inr (rejL hc)

/-- 🏁 **NegNum**: lo que no es una prueba en ℕ, `Prf` lo refuta. -/
theorem negNum {m y : Nat} (h : ¬ ProofN m y) : Prf (neg (PfF (numeralM m) (numeralM y))) := by
  rcases proofN_decide m y with hp | hp
  · exact absurd hp h
  · exact hp

/-- 🏁 **NegNum′** (con W1(ax), ADR‑148): si `dec y` no es teorema, `Prf` refuta cada candidata a prueba de `y`. -/
theorem negNum' {y : Nat} (h : ¬ Prf (dec y)) (m : Nat) : Prf (neg (PfF (numeralM m) (numeralM y))) :=
  negNum fun hp => h (w1Ax hp)

/-- Lo mismo sobre el código de una fórmula. -/
theorem negNum_formula {φ : Formula} (h : ¬ Prf φ) (m : Nat) :
    Prf (neg (PfF (numeralM m) (numeralM (codeNat φ)))) :=
  negNum' (by rw [dec_codeNat]; exact h) m

/-- Y con `formCode φ`, la forma de `posNum` (ADR‑149). -/
theorem negNum_formCode {φ : Formula} (h : ¬ Prf φ) (m : Nat) :
    Prf (neg (PfF (numeralM m) (ROBINSON_PlusPlus.Meta.Provability.formCode φ))) := by
  have he : Prf (ROBINSON_PlusPlus.Meta.Provability.formCode φ =eq numeralM (codeNat φ)) := by
    have e := ROBINSON_PlusPlus.Meta.CodeNumeralPrf.prf_formCode_numeral φ
    rw [← ROBINSON_PlusPlus.Meta.CheckArith.numeralM_eq] at e
    exact e
  refine prf_deduction ?_
  have hh := prfH_hyp_self (PfF (numeralM m) (ROBINSON_PlusPlus.Meta.Provability.formCode φ))
  exact PrfH.mp _ _ _ (prf_to_prfH (negNum_formula h m) _) (PrfH_and_intro (PrfH_and_elim_left hh)
    (PrfH_congr_In_left (prf_to_prfH he _) (PrfH_and_elim_right hh)))

/-! ## §5 · Controles (ADR‑146 §4) -/

/-- ✅ La hipótesis de `negNum` puede valer: la cadena vacía no prueba nada, y `Prf` lo refuta. -/
theorem control_negNum_vacia (y : Nat) : Prf (neg (PfF (numeralM 0) (numeralM y))) :=
  negNum (not_proofN_zero y)

/-- ✅ **…y sólo donde no hay prueba**: donde `ProofN` vale, `Prf` no refuta `PfF`, por la solidez en `MNV V₀`. -/
theorem control_exacta {m y : Nat} (h : ProofN m y) : ¬ Prf (neg (PfF (numeralM m) (numeralM y))) := by
  intro hp
  have hs := ROBINSON_PlusPlus.Meta.SolidezPrf.prf_sound ROBINSON_PlusPlus.Meta.Consistencia.estandar_MN hp
    (fun _ => 0)
  apply hs
  have em := ROBINSON_PlusPlus.Meta.ModeloEstandar.ev_numeralM (V := codeNatList axioms) (fun _ => 0) m
  have ey := ROBINSON_PlusPlus.Meta.ModeloEstandar.ev_numeralM (V := codeNatList axioms) (fun _ => 0) y
  simp only [PfF, land, chainOk, In, runFn, nil, zero, FOL.Metamath.Semantics.evalFormula,
    FOL.Metamath.Semantics.evalTerm, FOL.Metamath.Semantics.evalTerms, ROBINSON_PlusPlus.Meta.Consistencia.V₀_eq_codigo,
    em, ey, ROBINSON_PlusPlus.Meta.ModeloEstandar.MN_chainOk, ROBINSON_PlusPlus.Meta.ModeloEstandar.MN_runFn]
  exact h

/-- ✅ La hipótesis puede fallar: la prueba de un axioma ES una prueba, y `Prf` no la refuta. -/
theorem control_falla {a : Formula} (ha : List.Mem a axioms) :
    ¬ Prf (neg (PfF (numeralM (consN (lineaThy a) 0)) (numeralM (codeNat a)))) :=
  control_exacta (proofN_axioma ha)

end ROBINSON_PlusPlus.Meta.RosserNegNum

#print axioms ROBINSON_PlusPlus.Meta.RosserNegNum.chainOkN_decide
#print axioms ROBINSON_PlusPlus.Meta.RosserNegNum.proofN_decide
#print axioms ROBINSON_PlusPlus.Meta.RosserNegNum.negNum
#print axioms ROBINSON_PlusPlus.Meta.RosserNegNum.negNum_formCode
#print axioms ROBINSON_PlusPlus.Meta.RosserNegNum.prf_neg_lineOk_prem

/-! T08 en el módulo (ADR‑147): lo de esta etapa no nombra la semántica; los dos controles que usan la solidez en el
    modelo, sí. -/
#pureza ROBINSON_PlusPlus.Meta.RosserNegNum.chainOkN_decide ROBINSON_PlusPlus.Meta.RosserNegNum.proofN_decide
  ROBINSON_PlusPlus.Meta.RosserNegNum.negNum ROBINSON_PlusPlus.Meta.RosserNegNum.negNum'
  ROBINSON_PlusPlus.Meta.RosserNegNum.negNum_formula ROBINSON_PlusPlus.Meta.RosserNegNum.negNum_formCode
  ROBINSON_PlusPlus.Meta.RosserNegNum.control_negNum_vacia
  | ROBINSON_PlusPlus.Meta.RosserNegNum.control_exacta ROBINSON_PlusPlus.Meta.RosserNegNum.control_falla

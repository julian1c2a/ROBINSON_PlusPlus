/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.Hilbert
import ROBINSON_PlusPlus.Meta.CodeNumeralPrf
import FOL.Semantics

/-!
# `Meta/SolidezPrf.lean` — la SOLIDEZ de `Prf` en todo modelo ESTÁNDAR sobre `Nat` (ADR‑119/120)

`Estandar M`: `0`, `σ` y `::` estándar (`consN`), y los 142 verdaderos en `M`. Con eso, `prf_sound`: todo lo que
`Prf` demuestra es verdadero en `M`, por inducción sobre los 7 constructores de `Prf` y los 17 de `Prfᵢ`
(`prfI_sound`): `ind` pide `hzero`/`hsucc` y la inducción de `Nat`; `listInd`, `hcons`, `descompone` —todo `m + 1` es
un `cons` con cabeza y cola menores, sin basura desde ADR‑113— y la inducción fuerte `fuerte`; `qconf` es lógica pura.
`consistentH_de : Estandar M → ConsistentH`.

Viene de la sonda R2‑1‑2 de la ronda 2 de la auditoría (2026‑10‑02), corregida: un `∧` que se leía como
`Formula.and`, y fuera la obligación de `AnclaEq`, que ADR‑118 retiró.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false


open ROBINSON_PlusPlus.Meta.CodeNumeralPrf

namespace ROBINSON_PlusPlus.Meta.SolidezPrf

/-! §0 · Aritmética pura (SIN `open` de Axioms: `≤` sería el símbolo objeto) -/

theorem triN_succ' (s : Nat) : triN (s + 1) = triN s + (s + 1) := rfl

theorem le_triN : ∀ s : Nat, s ≤ triN s
  | 0 => Nat.le_refl _
  | s + 1 => by have := le_triN s; rw [triN_succ']; omega

/-- Copia de sondeos/CantorSobreyectivo.lean:72-94. -/
def wN : Nat → Nat
  | 0 => 0
  | n + 1 => if triN (wN n + 1) ≤ n + 1 then wN n + 1 else wN n

theorem wN_le : ∀ n : Nat, triN (wN n) ≤ n
  | 0 => by simp [wN, triN]
  | n + 1 => by
      have ih := wN_le n
      simp only [wN]
      by_cases h : triN (wN n + 1) ≤ n + 1
      · rw [if_pos h]; exact h
      · rw [if_neg h]; omega

theorem lt_wN_succ : ∀ n : Nat, n < triN (wN n + 1)
  | 0 => by simp [wN, triN]
  | n + 1 => by
      have ih := lt_wN_succ n
      simp only [wN]
      by_cases h : triN (wN n + 1) ≤ n + 1
      · rw [if_pos h]; have := triN_succ' (wN n + 1); omega
      · rw [if_neg h]; exact Nat.lt_of_not_le h

/-- Sin basura (ADR-113): todo m+1 es un cons con cabeza y cola MENORES.
    Control: con el consN viejo es FALSO en m = 0. -/
theorem descompone (m : Nat) : ∃ x y, And (consN x y = m + 1) (And (x < m + 1) (y < m + 1)) := by
  have h1 := wN_le m
  have h2 := lt_wN_succ m
  have h3 := triN_succ' (wN m)
  have h4 := le_triN (wN m)
  refine ⟨wN m - (m - triN (wN m)), m - triN (wN m), ?_, by omega, by omega⟩
  have hs : (wN m - (m - triN (wN m))) + (m - triN (wN m)) = wN m := by omega
  simp only [consN, hs]; omega

theorem fuerte (P : Nat → Prop) (h : ∀ n, (∀ m, m < n → P m) → P n) : ∀ n, P n := by
  have key : ∀ k m, m < k → P m := by
    intro k
    induction k with
    | zero => intro m hm; exact absurd hm (Nat.not_lt_zero m)
    | succ k ih =>
        intro m hm
        rcases Nat.lt_or_ge m k with hlt | hge
        · exact ih m hlt
        · have hmk : m = k := by omega
          subst hmk; exact h m ih
  exact fun n => key (n + 1) n (Nat.lt_succ_self n)

end ROBINSON_PlusPlus.Meta.SolidezPrf

section Modelo
open FOL FOL.Metamath.Semantics
open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Hilbert

namespace ROBINSON_PlusPlus.Meta.SolidezPrf

/-- Lo que A2/A3 tienen que entregar. -/
structure Estandar (M : Model Nat) : Prop where
  hzero : M.func zero_sym [] = 0
  hsucc : ∀ a, M.func succ_sym [a] = a + 1
  hcons : ∀ a b, M.func cons_sym [a, b] = consN a b
  haxs  : ∀ v, contextSatisfies M v axioms

theorem env1 (v : Nat → Nat) (a b : Nat) :
    shiftEnv (shiftEnv v a) b = updateEnv 1 (shiftEnv v b) a := by
  have h0 : shiftEnv v a = updateEnv 0 v a := by
    funext n; exact (updateEnv_zero v a n).symm
  rw [h0, shift_updateEnv_comm]

theorem env2 (v : Nat → Nat) (a b c : Nat) :
    shiftEnv (shiftEnv (shiftEnv v a) b) c = updateEnv 2 (shiftEnv (shiftEnv v b) c) a := by
  rw [env1 v a b, shift_updateEnv_comm]

variable {M : Model Nat}

theorem prfI_sound (hM : Estandar M) {φ : Formula} (h : Prfᵢ φ) : ∀ v, evalFormula M v φ := by
  induction h with
  | p1 A B => intro v hA _; exact hA
  | p2 A B C => intro v hABC hAB hA; exact hABC hA (hAB hA)
  | c1 A B => intro v hA hB; exact ⟨hA, hB⟩
  | c2 A B => intro v hAB; exact hAB.left
  | c3 A B => intro v hAB; exact hAB.right
  | j1 A B => intro v hA; exact Or.inl hA
  | j2 A B => intro v hB; exact Or.inr hB
  | j3 A B C =>
      intro v hAB hAC hBC
      rcases hAB with hA | hB
      · exact hAC hA
      · exact hBC hB
  | efq A => intro v hb; exact False.elim hb
  | q1 A t => intro v hall; exact (eval_substFormula_zero M v t A).mpr (hall _)
  | q2 A t => intro v hs; exact ⟨_, (eval_substFormula_zero M v t A).mp hs⟩
  | q3 A B =>
      intro v hall hex
      obtain ⟨d, hd⟩ := hex
      exact (eval_liftFormula_zero M v d B).mp (hall d hd)
  | eqrefl t => intro v; rfl
  | leibniz A t₁ t₂ =>
      intro v he hs
      have h1 := (eval_substFormula_zero M v t₁ A).mp hs
      have he' : evalTerm M v t₁ = evalTerm M v t₂ := he
      rw [he'] at h1
      exact (eval_substFormula_zero M v t₂ A).mpr h1
  | thy a ha => intro v; exact hM.haxs v a ha
  | mp A B _ _ ih1 ih2 => intro v; exact ih1 v (ih2 v)
  | gen A _ ih => intro v d; exact ih (shiftEnv v d)

theorem prf_sound (hM : Estandar M) {φ : Formula} (h : Prf φ) : ∀ v, evalFormula M v φ := by
  induction h with
  | incl h0 => exact prfI_sound hM h0
  | p3 A => intro v hnn; exact Classical.byContradiction hnn
  | ind A =>
      intro v
      simp only [ROBINSON_PlusPlus.Full.inductionFormula, evalFormula]
      intro h0 hst d
      have hz : evalTerm M v zero = 0 := by simp [zero, evalTerm, evalTerms, hM.hzero]
      have h0' : evalFormula M (shiftEnv v 0) A := by
        have := (eval_substFormula_zero M v zero A).mp h0; rwa [hz] at this
      induction d with
      | zero => exact h0'
      | succ n ih =>
          have hs := hst n ih
          have hsu : evalTerm M (shiftEnv v n) (succ (.var 0)) = n + 1 := by
            simp [succ, evalTerm, evalTerms, shiftEnv, hM.hsucc]
          rw [eval_substFormula_zero, hsu, env1, eval_liftFormula_ext] at hs
          exact hs
  | qconf P C =>
      intro v
      simp only [confinementFormula, evalFormula]
      intro hall hP d
      exact hall d ((eval_liftFormula_zero M v d P).mpr hP)
  | listInd A =>
      intro v
      simp only [listInductionFormula, evalFormula]
      intro h0 hst
      have hn : evalTerm M v nil = 0 := by simp [nil, zero, evalTerm, evalTerms, hM.hzero]
      have h0' : evalFormula M (shiftEnv v 0) A := by
        have := (eval_substFormula_zero M v nil A).mp h0; rwa [hn] at this
      refine fuerte (fun n => evalFormula M (shiftEnv v n) A) ?_
      intro n ih
      rcases n with _ | m
      · exact h0'
      · obtain ⟨x, y, hxy, _, hy⟩ := descompone m
        have hant : evalFormula M (shiftEnv (shiftEnv v x) y) (liftFormula 1 A) := by
          rw [env1, eval_liftFormula_ext]; exact ih y hy
        have hs := hst x y hant
        have hc : evalTerm M (shiftEnv (shiftEnv v x) y) (cons (.var 1) (.var 0)) = consN x y := by
          simp [cons, evalTerm, evalTerms, shiftEnv, hM.hcons]
        rw [eval_substFormula_zero, hc, hxy, env2, eval_liftFormula_ext, env1,
          eval_liftFormula_ext] at hs
        exact hs
  | mp A B _ _ ih1 ih2 => intro v; exact ih1 v (ih2 v)
  | gen A _ ih => intro v d; exact ih (shiftEnv v d)

/-- `ConsistentH` a partir de CUALQUIER modelo estándar; `estandar_MN` lo instancia en `MNV V₀`. -/
theorem consistentH_de (hM : Estandar M) : ConsistentH :=
  fun h => prf_sound hM h (fun _ => 0)

end ROBINSON_PlusPlus.Meta.SolidezPrf
end Modelo

#print axioms ROBINSON_PlusPlus.Meta.SolidezPrf.prf_sound
#print axioms ROBINSON_PlusPlus.Meta.SolidezPrf.consistentH_de

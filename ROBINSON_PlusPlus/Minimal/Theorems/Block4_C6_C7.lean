/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import ROBINSON_PlusPlus.Minimal.Axioms
import ROBINSON_PlusPlus.Minimal.Theorems.Block1
import ROBINSON_PlusPlus.Minimal.Theorems.Block2
import ROBINSON_PlusPlus.Minimal.Theorems.Block3
import ROBINSON_PlusPlus.Minimal.Theorems.Block4
import ROBINSON_PlusPlus.Minimal.Theorems.Block4_C5

import FOL.FOL
import FOL.Tactics
import FOL.Theorems.Eq
import FOL.Theorems.Impl
import FOL.Theorems.Neg
import FOL.Theorems.Derived
import FOL.Theorems.Quantifiers
import FOL.Deduction

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Minimal.Theorems.Block1
open ROBINSON_PlusPlus.Minimal.Theorems.Block2
open ROBINSON_PlusPlus.Minimal.Theorems.Block3
open ROBINSON_PlusPlus.Minimal.Theorems.Block4
open ROBINSON_PlusPlus.Minimal.Theorems.Block4_C5

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Minimal.Theorems.Block4_C6_C7

/-!
## BLOQUE IV — TEOREMAS C6 Y C7 (SOBREYECTIVIDAD Y UNICIDAD)
-/

-- The context for all theorems in this system is the set of axioms.
def Γ := axioms

/-!
### Fase 9.2: Sobreyectividad y Unicidad Proyectiva
-/

-- Lema A (privado): liftTerm 1 (liftTerm 0 t) = liftTerm 0 (liftTerm 0 t)
-- Ambas expresiones incrementan TODOS los índices de variable en 2.
-- Para .var n: liftTerm 0 da .var (n+1), liftTerm 1 sobre ese da .var (n+2).
--              liftTerm 0 sobre .var (n+1) también da .var (n+2). ✓
-- Necesario para que substTerm_liftTerm (c=1) pueda eliminar liftTerm 0 (liftTerm 0 a).
mutual
private theorem lift_01_eq_00 (t : Term) :
    liftTerm 1 (liftTerm 0 t) = liftTerm 0 (liftTerm 0 t) := by
  cases t with
  | var n =>
    -- Para n : Nat, el kernel reduce n < 0 = False definitionally
    -- (Nat.ble (n+1) 0 = false por def, ya que n+1 = Nat.succ _).
    -- Ambos lados = .var (n+2). Se cierra por reflexividad.
    rfl
  | func f ts =>
    simp only [liftTerm]
    congr 1
    exact lift_01_eq_00_list ts

private theorem lift_01_eq_00_list (ts : List Term) :
    liftTerms 1 (liftTerms 0 ts) = liftTerms 0 (liftTerms 0 ts) := by
  cases ts with
  | nil => rfl
  | cons t ts' =>
    -- simp [liftTerms] despliega la lista concreta (a diferencia de unfold
    -- que deja el match en la forma stuck para argumentos no-WHNF)
    simp only [liftTerms]
    rw [lift_01_eq_00 t, lift_01_eq_00_list ts']
end

-- Helper theorem for left cancellation on addition.
-- Proof strategy: ax27_add_left_cancel = ∀a∀b∀c, (add a c = add b c) ⇒ a = b.
-- Triple spec introduces liftTerm 0 (liftTerm 0 a) in the type.
-- Using lift_01_eq_00 (Lema A) + FOL.substTerm_liftTerm, simp reduces the type
-- to the desired formula.
theorem add_left_cancel {a b c : Term}
  (h : Γ ⊢ ((add a c) =eq (add b c))) :
    Γ ⊢ (a =eq b) := by
  have h_ax27 := ax (by simp [axioms, ax27_add_left_cancel] : ax27_add_left_cancel ∈ axioms)
  have h_imp : Γ ⊢ ((add a c =eq add b c) ⇒ (a =eq b)) := by
    have h1 := spec h_ax27 a
    have h2 := spec h1 b
    have h3 := spec h2 c
    -- simp (sin only) incluye ite_true, ite_false, aritmética Nat,
    -- necesarias porque substFormula genera "0 + 1", "0 + 1 + 1" en vez de "1", "2".
    -- lift_01_eq_00 convierte liftTerm 0 (liftTerm 0 a) → liftTerm 1 (liftTerm 0 a)
    -- para que substTerm_liftTerm pueda disparar con c=1.
    simp [substFormula, substTerm, substTerms,
          add, add_sym,
          ← lift_01_eq_00,
          FOL.substTerm_liftTerm] at h3
    exact h3
  exact mp h_imp h

-- ============================================================================
-- Inverse functions (constructive definitions using `sub` from Axioms.lean)
-- ============================================================================
-- `w_of_c c` recupera el `w` único del Lema C5: w = div2(pred(√(8c+1))).
-- Coincide con `w_candidate` exportado por Block4_C5 (preferir aquel; este
-- alias se mantiene por compatibilidad).
def w_of_c (c : Term) : Term := w_candidate c

-- Dado el `w` de C5 y `k` tal que w(w+1) = 2k (vía `parity_lemma`),
-- definimos `y = c − k`, lo que da 2y = 2c − w(w+1) en el rango b ≤ a por ax29.
-- En la prueba real, `k` se obtiene por `ex_elim (parity_lemma w)`; el alias
-- a continuación es solo notacional para el caso «cerrado» en el que k = div2(w(w+1)).
def y_of_c (c : Term) : Term := sub c (div2 (mul (w_candidate c) (succ (w_candidate c))))
def x_of_c (c : Term) : Term := sub (w_candidate c) (y_of_c c)

-- Teo C6 (Sobreyectividad de Cantor): ∀ c, ∃ x, ∃ y, Cantor(x,y,c).
-- Nota: `c` aparece como `liftTerm 0 (liftTerm 0 c)` bajo el doble binder ∃∃
-- (forma De Bruijn correcta; al instanciar con `ex_intro x` luego `ex_intro y`,
--  ambos lifts se cancelan vía `FOL.substTerm_liftTerm` y `FOL.substTerm_liftLift`).
theorem cantor_surjectivity (c : Term) :
    Γ ⊢ ex (ex (is_cantor (.var 1) (.var 0) (liftTerm 0 (liftTerm 0 c)))) := by
  have h_ax12 := ax (by simp [axioms] : ax12_mul_distrib ∈ axioms)
  have h_ax18 := ax (by simp [axioms] : ax18_lt_irrefl ∈ axioms)
  have h_ax19 := ax (by simp [axioms] : ax19_lt_trichotomy ∈ axioms)
  have h_ax29 := ax (by simp [axioms] : ax29_sub_witness ∈ axioms)
  -- ============================================================
  -- Paso 1: extraer w con cotas C5
  -- ============================================================
  have h_C5 := lemma_C5 c
  apply ex_elim h_C5
  intro w h_w_raw
  simp [substFormula, substTerm, substTerms, land, le, lt, mul, succ,
        FOL.substTerm_liftTerm] at h_w_raw
  -- h_w_raw : land (le (mul w (succ w)) (mul two c))
  --                (lt (mul two c) (mul (succ w) (succ (succ w))))
  have h_w_lo : Γ ⊢ le (mul w (succ w)) (mul two c) := Axioms.and_elim_left h_w_raw
  have h_w_hi : Γ ⊢ lt (mul two c) (mul (succ w) (succ (succ w))) :=
    Axioms.and_elim_right h_w_raw
  -- ============================================================
  -- Paso 2: extraer k tal que w(w+1) = 2k (parity_lemma)
  -- ============================================================
  have h_par := parity_lemma w
  apply ex_elim h_par
  intro k h_k_raw
  simp [substFormula, substTerm, substTerms, mul, succ,
        FOL.substTerm_liftTerm] at h_k_raw
  -- h_k_raw : mul w (succ w) =eq mul two k
  -- ============================================================
  -- Paso 3: k ≤ c y derivar 2k + 2y = 2c donde y = sub c k
  -- ============================================================
  have h_2k_le_2c : Γ ⊢ le (mul two k) (mul two c) :=
    le_rewrite h_w_lo h_k_raw (eq_refl _)
  have h_2_pos : Γ ⊢ lt zero two := lt_zero_succ one
  have h_k_le_c : Γ ⊢ le k c := le_of_mul_le_mul_left h_2k_le_2c h_2_pos
  -- ax29 (a:=c, b:=k): k ≤ c ⇒ k + (c − k) = c
  have h_k_plus_y_eq_c : Γ ⊢ (add k (sub c k) =eq c) := by
    have h_imp : Γ ⊢ (le k c ⇒ (add k (sub c k) =eq c)) := by
      have h := spec (spec h_ax29 c) k
      simp [substFormula, substTerm, substTerms, le, lt, add, sub,
            liftTerm, liftTerms, FOL.substTerm_liftTerm,
            FOL.substTerm_liftLift] at h
      exact h
    exact mp h_imp h_k_le_c
  -- 2·(k + y) = 2k + 2y  [ax12 distribución]
  have h_two_dist : Γ ⊢
      (mul two (add k (sub c k)) =eq add (mul two k) (mul two (sub c k))) := by
    have h := spec (spec (spec h_ax12 two) k) (sub c k)
    simp [substFormula, substTerm, substTerms, mul, add, sub,
          liftTerm, liftTerms, FOL.substTerm_liftTerm,
          FOL.substTerm_liftLift] at h
    exact h
  -- 2·(k+y) = 2c (multiplicando la igualdad k+y=c por 2 a la izquierda)
  have h_2_kpy_eq_2c : Γ ⊢ (mul two (add k (sub c k)) =eq mul two c) :=
    eq_congr_mul_left h_k_plus_y_eq_c
  -- 2k + 2y = 2c
  have h_2k_plus_2y_eq_2c : Γ ⊢ (add (mul two k) (mul two (sub c k)) =eq mul two c) :=
    FOL.derive_eq_trans (eq_symm h_two_dist) h_2_kpy_eq_2c
  -- ============================================================
  -- Paso 4: y ≤ w (por tricotomía y contradicción usando h_w_hi)
  -- ============================================================
  have h_y_le_w : Γ ⊢ le (sub c k) w := by
    have h_tric : Γ ⊢ (lt (sub c k) w ∨ (sub c k =eq w) ∨ lt w (sub c k)) := by
      have h := spec (spec h_ax19 (sub c k)) w
      simp [substFormula, substTerm, substTerms, lt, FOL.substTerm_liftTerm] at h
      exact h
    apply Axioms.or_elim h_tric
    · intro h_lt; exact Axioms.or_intro_left h_lt
    · intro h23
      apply Axioms.or_elim h23
      · intro h_eq; exact Axioms.or_intro_right h_eq
      · intro h_w_lt_y
        -- w < y ⇒ succ w ≤ y ⇒ 2(succ w) ≤ 2y ⇒
        --   w(w+1) + 2(succ w) ≤ w(w+1) + 2y = 2c
        --   pero (w+1)(w+2) = w(w+1) + 2(succ w) y 2c < (w+1)(w+2) ⇒ contradicción
        apply false_elim
        have h_succ_w_le_y : Γ ⊢ le (succ w) (sub c k) := succ_le_of_lt h_w_lt_y
        have h_2sw_le_2y : Γ ⊢ le (mul two (succ w)) (mul two (sub c k)) :=
          le_mul_left h_succ_w_le_y
        have h_chain : Γ ⊢ le
            (add (mul w (succ w)) (mul two (succ w)))
            (add (mul w (succ w)) (mul two (sub c k))) :=
          le_add_const_of_le_left h_2sw_le_2y
        -- (w+1)(w+2) =eq w(w+1) + 2(w+1)
        have h_expand : Γ ⊢
            (mul (succ w) (succ (succ w)) =eq add (mul w (succ w)) (mul two (succ w))) :=
          expand_succ_succ w
        -- add (mul w (succ w)) (mul two y) =eq mul two c
        have h_rewrite_lhs : Γ ⊢
            (add (mul w (succ w)) (mul two (sub c k)) =eq
             add (mul two k) (mul two (sub c k))) :=
          eq_congr_add_right h_k_raw
        have h_eq_2c : Γ ⊢
            (add (mul w (succ w)) (mul two (sub c k)) =eq mul two c) :=
          FOL.derive_eq_trans h_rewrite_lhs h_2k_plus_2y_eq_2c
        -- (w+1)(w+2) ≤ 2c
        have h_ww1_le_2c : Γ ⊢ le (mul (succ w) (succ (succ w))) (mul two c) :=
          le_rewrite h_chain (eq_symm h_expand) h_eq_2c
        -- contradicción: 2c < (w+1)(w+2) ≤ 2c ⇒ 2c < 2c
        have h_irr : Γ ⊢ neg (lt (mul two c) (mul two c)) := by
          have h := spec h_ax18 (mul two c); simp [lt] at h; exact h
        exact mp h_irr (lt_le_trans h_w_hi h_ww1_le_2c)
  -- ============================================================
  -- Paso 5: definir x = sub w y; derivar x + y = w; verificar is_cantor
  -- ============================================================
  -- ax29 (a:=w, b:=y): y ≤ w ⇒ y + (w − y) = w
  have h_y_plus_x_eq_w : Γ ⊢ (add (sub c k) (sub w (sub c k)) =eq w) := by
    have h_imp : Γ ⊢
        (le (sub c k) w ⇒ (add (sub c k) (sub w (sub c k)) =eq w)) := by
      have h := spec (spec h_ax29 w) (sub c k)
      simp [substFormula, substTerm, substTerms, le, lt, add, sub,
            liftTerm, liftTerms, FOL.substTerm_liftTerm,
            FOL.substTerm_liftLift] at h
      exact h
    exact mp h_imp h_y_le_w
  -- x + y = w  (conmutar)
  have h_x_plus_y_eq_w : Γ ⊢ (add (sub w (sub c k)) (sub c k) =eq w) :=
    FOL.derive_eq_trans (add_comm' (sub w (sub c k)) (sub c k)) h_y_plus_x_eq_w
  -- cantor_poly x y =eq mul two c
  -- (x+y)(x+y+1) =eq w(w+1) (congruencia con h_x_plus_y_eq_w)
  have h_poly_left : Γ ⊢
      (mul (add (sub w (sub c k)) (sub c k)) (succ (add (sub w (sub c k)) (sub c k))) =eq
       mul w (succ w)) :=
    FOL.derive_eq_trans (eq_congr_mul_right h_x_plus_y_eq_w)
      (eq_congr_mul_left (eq_congr_succ h_x_plus_y_eq_w))
  -- = 2k (vía h_k_raw)
  have h_poly_left_2k : Γ ⊢
      (mul (add (sub w (sub c k)) (sub c k)) (succ (add (sub w (sub c k)) (sub c k))) =eq
       mul two k) :=
    FOL.derive_eq_trans h_poly_left h_k_raw
  -- cantor_poly x y =eq 2k + 2y
  have h_cantor_poly_2k_2y : Γ ⊢
      (add (mul (add (sub w (sub c k)) (sub c k)) (succ (add (sub w (sub c k)) (sub c k))))
           (mul two (sub c k)) =eq
       add (mul two k) (mul two (sub c k))) :=
    eq_congr_add_right h_poly_left_2k
  -- = mul two c
  have h_cantor_eq : Γ ⊢
      (add (mul (add (sub w (sub c k)) (sub c k)) (succ (add (sub w (sub c k)) (sub c k))))
           (mul two (sub c k)) =eq
       mul two c) :=
    FOL.derive_eq_trans h_cantor_poly_2k_2y h_2k_plus_2y_eq_2c
  -- is_cantor (sub w y) (sub c k) c := mul two c =eq cantor_poly (sub w y)(sub c k)
  have h_is_cantor : Γ ⊢
      (mul two c =eq
       add (mul (add (sub w (sub c k)) (sub c k)) (succ (add (sub w (sub c k)) (sub c k))))
           (mul two (sub c k))) :=
    eq_symm h_cantor_eq
  -- ============================================================
  -- Paso 6: ex_intro x, ex_intro y; simp reduce el doble lift
  -- ============================================================
  apply ex_intro (sub w (sub c k))
  apply ex_intro (sub c k)
  simp [substFormula, substTerm, substTerms, is_cantor, cantor_poly,
        mul, add, succ, two, one, zero, sub,
        FOL.substTerm_liftTerm, FOL.substTerm_liftLift]
  exact h_is_cantor

-- Conmutatividad de la suma (helper local).
private theorem add_comm_c (a b : Term) : Γ ⊢ (add a b =eq add b a) := by
  have h := spec (spec (ax (by simp [axioms] : ax6_add_comm ∈ axioms)) a) b
  simp [substFormula, substTerm, substTerms, add, liftTerm, liftTerms, FOL.substTerm_liftTerm] at h
  exact h

-- Teo C7: Cantor(x,y,c) ∧ Cantor(x',y',c) ⇒ x=x' ∧ y=y' (Unicidad Proyectiva)
theorem cantor_uniqueness (x y x' y' c : Term) :
    Γ ⊢ land (is_cantor x y c) (is_cantor x' y' c) ⇒ land (x =eq x') (y =eq y') := by
  apply Axioms.imp_intro; intro h_land
  have h_xy : Γ ⊢ (mul two c =eq add (mul (add x y) (succ (add x y))) (mul two y)) :=
    Axioms.and_elim_left h_land
  have h_x'y' : Γ ⊢ (mul two c =eq add (mul (add x' y') (succ (add x' y'))) (mul two y')) :=
    Axioms.and_elim_right h_land
  -- C5 bounds + uniqueness ⇒ x+y = x'+y'
  have h_w  := cantor_bounds h_xy
  have h_w' := cantor_bounds h_x'y'
  have h_w_eq : Γ ⊢ (add x y =eq add x' y') := lemma_C5_unique h_w h_w'
  -- w(w+1) = w'(w'+1)
  have h_W_eq : Γ ⊢ (mul (add x y) (succ (add x y)) =eq mul (add x' y') (succ (add x' y'))) :=
    FOL.derive_eq_trans (eq_congr_mul_right h_w_eq) (eq_congr_mul_left (eq_congr_succ h_w_eq))
  -- W + 2y = W + 2y'
  have h_WW : Γ ⊢ (add (mul (add x y) (succ (add x y))) (mul two y) =eq
      add (mul (add x y) (succ (add x y))) (mul two y')) :=
    FOL.derive_eq_trans (FOL.derive_eq_trans (eq_symm h_xy) h_x'y')
      (eq_congr_add_right (eq_symm h_W_eq))
  -- conmutar + cancelar ⇒ 2y = 2y'
  have h_2y_eq : Γ ⊢ (mul two y =eq mul two y') := by
    have hcomm : Γ ⊢ (add (mul two y) (mul (add x y) (succ (add x y))) =eq
        add (mul two y') (mul (add x y) (succ (add x y)))) :=
      FOL.derive_eq_trans (add_comm_c (mul two y) (mul (add x y) (succ (add x y))))
        (FOL.derive_eq_trans h_WW (add_comm_c (mul (add x y) (succ (add x y))) (mul two y')))
    exact add_left_cancel hcomm
  -- 2y = 2y' ⇒ y = y'
  have h_y_eq : Γ ⊢ (y =eq y') := by
    have h28 : Γ ⊢ ((mul two y =eq mul two y') ⇒ (y =eq y')) := by
      have hh := spec (spec teo_2_11 y) y'
      simp [substFormula, substTerm, substTerms, mul, two, one, FOL.substTerm_liftTerm] at hh
      exact hh
    exact mp h28 h_2y_eq
  -- x+y = x'+y ⇒ x = x'
  have h_x_eq : Γ ⊢ (x =eq x') := by
    have h_axy : Γ ⊢ (add x y =eq add x' y) :=
      FOL.derive_eq_trans h_w_eq (eq_congr_add_left (eq_symm h_y_eq))
    exact add_left_cancel h_axy
  exact Axioms.and_intro h_x_eq h_y_eq

end ROBINSON_PlusPlus.Minimal.Theorems.Block4_C6_C7

-- Exports
export ROBINSON_PlusPlus.Minimal.Theorems.Block4_C6_C7 (
  cantor_surjectivity
  cantor_uniqueness
)

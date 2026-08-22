/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.NatMulPrf
import ROBINSON_PlusPlus.Meta.CantorMonoPrf
import ROBINSON_PlusPlus.Meta.StrongInductionPrf

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.NatArithPrf
open ROBINSON_PlusPlus.Meta.NatOrderPrf
open ROBINSON_PlusPlus.Meta.NatMulPrf
open ROBINSON_PlusPlus.Meta.CantorMonoPrf
open ROBINSON_PlusPlus.Meta.StrongInductionPrf

set_option maxHeartbeats 1000000

namespace ROBINSON_PlusPlus.Meta.Div2ParityPrf

/-!
## META — PARIDAD y `div2`: **cadena COMPLETA** hacia `prf_cons_eval`

Frente **S4** de `PLAN-SORTES.md`: la evaluación provable del emparejamiento de Cantor sobre
numerales, que es lo único que separa a la reparación de la inconsistencia de estar completa para
Gödel I (ver `sondeos/README.md` y la memoria `project-reparacion-via-numeral`).

**La cadena completa** hacia `prf_cons_eval (a b) : Prf (cons ā b̄ =eq numeral (consN a b))`:

| paso | enunciado | estado |
|---|---|---|
| **L1** | `lt x y ⇒ lt (x·2) (y·2)` | ✅ **este módulo** |
| **L2** | `(x·2 =eq y·2) ⇒ (x =eq y)` | ✅ **este módulo** |
| **L3** | `mod2 (x·2) =eq zero` | ✅ **este módulo** |
| **L4** | `div2 (x·2) =eq x` | ✅ **este módulo** |
| **L5** | `div2 (numeral (2m)) =eq numeral m` | ✅ **este módulo — HITO de S4** |

Todo en forma **OBJETO** (`x` abstracto ⟹ vale para todos los numerales a la vez) y **net‑0**:
`ax9`, `ax10`, `ax12`, `ax13` y `ax17`/`ax21` ya son axiomas de la teoría, así que portarlos a `Prf`
no añade nada.

**Además este módulo cubre dos huecos que no estaban registrados**: `ax12_mul_distrib` y el
homomorfismo `numeral a · numeral b = numeral (a·b)` **no existían a nivel `Prf`** (sólo la versión
ω, en `Full/Numerals.lean`, que es de la capa `Derives` y no sirve aquí).
-/

/-! ### Piezas que faltaban del producto -/

/-- **Distributividad** `a·(b+c) = a·b + a·c` — instancia de `ax12_mul_distrib`. -/
theorem prf_mul_distrib (a b c : Term) :
    Prf (mul a (add b c) =eq add (mul a b) (mul a c)) := by
  have hh := prf_spec (prf_spec (prf_spec
    (prf_ax (show ax12_mul_distrib ∈ axioms by simp [axioms])) a) b) c
  simp [substFormula, substTerm, substTerms, mul, add,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

/-- Congruencia de `·` en el **segundo** argumento, en contexto (`NatMulPrf` sólo tenía la del
    primero). -/
theorem PrfH_eq_congr_mul2 {Γ : List Formula} {t₁ t₂ : Term} (c : Term)
    (h : PrfH Γ (t₁ =eq t₂)) : PrfH Γ (mul c t₁ =eq mul c t₂) := by
  let f : Formula := Formula.eq (mul (liftTerm 0 c) (liftTerm 0 t₁)) (mul (liftTerm 0 c) (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (mul c t₁) (mul c s) := by
    intro s
    simp only [f, substFormula, mul, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS t₂) ▸ PrfH_leibniz_subst (A := f) h ((hS t₁) ▸ prf_to_prfH (prf_refl (mul c t₁)) Γ)

/-! ### Homomorfismo del producto sobre numerales

Espejo exacto de `prf_numeral_add` (`Meta/ArithPrf.lean:93`). Inducción **meta** en `b`: para `b`
simbólico queda una aplicación, Lean no la despliega (medido en el sondeo S3). -/

/-- `numeral a · numeral b = numeral (a·b)` sobre `Full.numeral`. -/
theorem prf_numeral_mul (a b : Nat) :
    Prf (mul (ROBINSON_PlusPlus.Full.numeral a) (ROBINSON_PlusPlus.Full.numeral b)
      =eq ROBINSON_PlusPlus.Full.numeral (a * b)) := by
  induction b with
  | zero =>
      show Prf (mul (ROBINSON_PlusPlus.Full.numeral a) zero =eq zero)
      exact prf_mul_zero _
  | succ k ih =>
      show Prf (mul (ROBINSON_PlusPlus.Full.numeral a)
        (succ (ROBINSON_PlusPlus.Full.numeral k)) =eq ROBINSON_PlusPlus.Full.numeral (a * (k+1)))
      have h1 := prf_mul_succ (ROBINSON_PlusPlus.Full.numeral a) (ROBINSON_PlusPlus.Full.numeral k)
      have h2 : Prf (add (mul (ROBINSON_PlusPlus.Full.numeral a) (ROBINSON_PlusPlus.Full.numeral k))
                       (ROBINSON_PlusPlus.Full.numeral a)
                  =eq add (ROBINSON_PlusPlus.Full.numeral (a*k))
                          (ROBINSON_PlusPlus.Full.numeral a)) :=
        prf_eq_congr_add1 _ ih
      have h3 := prf_numeral_add (a*k) a
      have hn : a * (k+1) = a*k + a := Nat.mul_succ a k
      rw [hn]
      exact prf_eq_trans h1 (prf_eq_trans h2 h3)

/-- Igual, sobre `Godel.numeral` — la que usan `formCode`/`termCode`. -/
theorem prf_gnum_mul (a b : Nat) :
    Prf (mul (numeral a) (numeral b) =eq numeral (a * b)) := by
  rw [numeral_bridge, numeral_bridge, numeral_bridge]
  exact prf_numeral_mul a b

/-! ### L1 — monotonía ESTRICTA del doble

De `x < y` sale (por `ax13`) un testigo `k` con `x + σk = y`. Entonces

```
y·2 = 2·(x + σk) = 2·x + 2·σk = x·2 + (2·k + 2)   y   2·k + 2 = σ(2·k + 1)
```

luego el testigo de `x·2 < y·2` es **`2·k + 1`**. Una sola eliminación de `∃`. -/

/-- **L1** — `x < y ⟹ x·2 < y·2`. Lo consumen L2 (cancelación) y el caso `mod2 = 1` de L3. -/
theorem prf_mul_two_lt_mono (x y : Term) :
    Prf (lt x y ⇒ lt (mul x two) (mul y two)) := by
  have himp : Prf (Formula.ex (Formula.eq (add (liftTerm 0 x) (succ (.var 0))) (liftTerm 0 y))
      ⇒ lt (mul x two) (mul y two)) := by
    refine prf_ex_elim_imp ?_
    show PrfH [Formula.eq (add (liftTerm 0 x) (succ (.var 0))) (liftTerm 0 y)]
      (lt (mul (liftTerm 0 x) two) (mul (liftTerm 0 y) two))
    let X : Term := liftTerm 0 x
    let Y : Term := liftTerm 0 y
    let K : Term := .var 0
    let Γ : List Formula := [Formula.eq (add X (succ K)) Y]
    refine PrfH_lt_intro (mul X two) (mul Y two) (add (mul two K) one) ?_
    -- (a) `σ(2K + 1) = 2K + 2 = 2·σK`  (`two = σ one` es defeq)
    have ha : Prf (succ (add (mul two K) one) =eq mul two (succ K)) :=
      prf_eq_trans (prf_eq_symm (prf_add_succ_t (mul two K) one))
        (prf_eq_symm (prf_mul_succ two K))
    -- (b) `X·2 + 2·σK = 2·X + 2·σK = 2·(X + σK)`
    have hb : Prf (add (mul X two) (mul two (succ K)) =eq mul two (add X (succ K))) :=
      prf_eq_trans (prf_eq_congr_add1 _ (prf_mul_comm X two))
        (prf_eq_symm (prf_mul_distrib two X (succ K)))
    -- cadena: `X·2 + σ(2K+1) = 2·(X + σK) = 2·Y = Y·2`
    refine PrfH_eq_trans (prf_to_prfH (prf_eq_congr_add2 (mul X two) ha) _) ?_
    refine PrfH_eq_trans (prf_to_prfH hb _) ?_
    refine PrfH_eq_trans (PrfH_eq_congr_mul2 two (prfH_hyp_self _)) ?_
    exact prf_to_prfH (prf_mul_comm two Y) _
  exact prf_deduction
    (PrfH.mp _ _ _ (prf_to_prfH himp _) (PrfH_iff_mp (prf_lt_iff x y) (prfH_hyp_self _)))

/-! ### L2 — cancelación del doble

Por tricotomía: las dos ramas estrictas se cierran con **L1** más `prf_lt_irrefl`; la del medio
**es** la conclusión. -/

/-- **L2** — `x·2 = y·2 ⟹ x = y`. -/
theorem prf_mul_two_cancel (x y : Term) :
    Prf ((mul x two =eq mul y two) ⇒ (x =eq y)) := by
  refine prf_deduction ?_
  refine PrfH_or_elim (prf_to_prfH (prf_lt_trichotomy x y) _) ?_ ?_
  · -- `x < y` ⟹ `x·2 < y·2`, y con la hipótesis sale `y·2 < y·2`
    have hxy : PrfH [lt x y, mul x two =eq mul y two] (lt x y) :=
      PrfH.hyp _ _ (List.Mem.head _)
    have heq : PrfH [lt x y, mul x two =eq mul y two] (mul x two =eq mul y two) :=
      PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
    have hlt : PrfH [lt x y, mul x two =eq mul y two] (lt (mul x two) (mul y two)) :=
      PrfH.mp _ _ _ (prf_to_prfH (prf_mul_two_lt_mono x y) _) hxy
    exact PrfH_absurd_lt (mul y two) (PrfH_lt_subst1 heq hlt)
  · refine PrfH_or_elim (PrfH.hyp _ _ (List.Mem.head _)) ?_ ?_
    · -- `x = y`: es la conclusión
      exact PrfH.hyp _ _ (List.Mem.head _)
    · -- `y < x`: simétrico
      have hyx : PrfH [lt y x, lor (Formula.eq x y) (lt y x), mul x two =eq mul y two]
          (lt y x) := PrfH.hyp _ _ (List.Mem.head _)
      have heq : PrfH [lt y x, lor (Formula.eq x y) (lt y x), mul x two =eq mul y two]
          (mul x two =eq mul y two) :=
        PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
      have hlt : PrfH [lt y x, lor (Formula.eq x y) (lt y x), mul x two =eq mul y two]
          (lt (mul y two) (mul x two)) :=
        PrfH.mp _ _ _ (prf_to_prfH (prf_mul_two_lt_mono y x) _) hyx
      exact PrfH_absurd_lt (mul y two) (PrfH_lt_subst2 heq hlt)

/-! ### L3 — el doble es PAR

`ax17` da `D·2 + M = x·2` con `D = div2 (x·2)`, `M = mod2 (x·2)`; `ax21` da `M ∈ {0,1}`.
Si `M = 1` entonces `σ(D·2) = x·2`, y de ahí:

* `D·2 < x·2` ⟹ (cancelación multiplicativa, `prf_lt_of_mul_lt_mul_right`) `D < x`;
* `x·2 = σ(D·2) < σσ(D·2) = (σD)·2` ⟹ `x < σD` ⟹ (`prf_le_of_lt_succ`) `x ≤ D`;

y `D < x ≤ D` da `D < D`. **No usa L1**: le basta la cancelación que ya existía. -/

/-- **L3** — `mod2 (x·2) = 0`. -/
theorem prf_mod2_double (x : Term) : Prf (mod2 (mul x two) =eq zero) := by
  refine prf_or_elim (prf_mod2_range (mul x two)) (prf_deduction (prfH_hyp_self _)) ?_
  refine prf_deduction ?_
  let D : Term := div2 (mul x two)
  let M : Term := mod2 (mul x two)
  let Γ : List Formula := [M =eq one]
  have hM : PrfH Γ (M =eq one) := prfH_hyp_self _
  -- `σ(D·2) = x·2`
  have hkey : PrfH Γ (succ (mul D two) =eq mul x two) := by
    have h1 : PrfH Γ (add (mul D two) M =eq add (mul D two) one) :=
      PrfH_eq_congr_add2 (mul D two) hM
    have h2 : PrfH Γ (add (mul D two) M =eq succ (mul D two)) :=
      PrfH_eq_trans h1 (prf_to_prfH (prf_add_one (mul D two)) _)
    exact PrfH_eq_trans (PrfH_eq_symm h2) (prf_to_prfH (prf_div_mod_eq (mul x two)) _)
  -- `D < x`
  have hDx : PrfH Γ (lt D x) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_lt_of_mul_lt_mul_right D x two) _)
      (PrfH_lt_subst2 hkey (prf_to_prfH (prf_lt_succ_self_cm (mul D two)) _))
  -- `(σD)·2 = σσ(D·2)`
  have hms : Prf (mul (succ D) two =eq succ (succ (mul D two))) :=
    prf_eq_trans (prf_mul_comm (succ D) two)
      (prf_eq_trans (prf_mul_succ two D)
        (prf_eq_trans (prf_eq_congr_add1 two (prf_mul_comm two D))
          (prf_eq_trans (prf_add_succ_t (mul D two) one)
            (prf_eq_congr_succ (prf_add_one (mul D two))))))
  -- `x·2 < (σD)·2` ⟹ `x < σD` ⟹ `x ≤ D`
  have hle : PrfH Γ (le x D) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_le_of_lt_succ x D) _)
      (PrfH.mp _ _ _ (prf_to_prfH (prf_lt_of_mul_lt_mul_right x (succ D) two) _)
        (PrfH_lt_subst2 (prf_to_prfH (prf_eq_symm hms) _)
          (PrfH_lt_subst1 hkey (prf_to_prfH (prf_lt_succ_self_cm (succ (mul D two))) _))))
  -- `D < x ≤ D` ⟹ `D < D` ⟹ ex falso
  exact PrfH_absurd_lt D
    (PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (prf_lt_le_trans D x D) _) hDx) hle)

/-! ### P2 — congruencia de `div2` (Leibniz objeto)

No existía a nivel `Prf` (la de `Full/Mod2.lean` es de la capa ω). -/

/-- `t₁ = t₂ ⟹ div2 t₁ = div2 t₂`. -/
theorem prf_eq_congr_div2 {t₁ t₂ : Term} (h : Prf (t₁ =eq t₂)) :
    Prf (div2 t₁ =eq div2 t₂) := by
  let f : Formula := Formula.eq (div2 (liftTerm 0 t₁)) (div2 (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (div2 t₁) (div2 s) := by
    intro s
    simp only [f, substFormula, div2, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS t₂) ▸ prf_leibniz_subst (A := f) h ((hS t₁) ▸ prf_refl (div2 t₁))

/-! ### L4 — `div2` deshace el doble

`ax17` da `D·2 + M = x·2` con `D = div2 (x·2)`; **L3** pone `M = 0`, luego `D·2 = x·2`; y **L2**
cancela. Tres líneas de cadena: todo el trabajo estaba en L1–L3. -/

/-- **L4** — `div2 (x·2) = x`. -/
theorem prf_div2_double (x : Term) : Prf (div2 (mul x two) =eq x) := by
  let D : Term := div2 (mul x two)
  have h1 : Prf (add (mul D two) (mod2 (mul x two)) =eq add (mul D two) zero) :=
    prf_eq_congr_add2 (mul D two) (prf_mod2_double x)
  have h2 : Prf (add (mul D two) zero =eq mul D two) := prf_add_zero_t (mul D two)
  have h3 : Prf (mul D two =eq mul x two) :=
    prf_eq_trans (prf_eq_symm (prf_eq_trans h1 h2)) (prf_div_mod_eq (mul x two))
  exact prf_mp (prf_mul_two_cancel D x) h3

/-! ### L5 — la forma NUMERAL: **el hito del frente S4**

Instancia de L4 en `numeral m`, cruzada con `prf_gnum_mul m 2` (`numeral 2 = two` es **defeq**).
Es la pieza de la que cuelgan `prf_cons_eval` → `prf_formCode_numeral` (= la `hFN` que el piloto
del lema diagonal, `sondeos/PilotoDiagonal.lean`, asumía). -/

/-- **L5** — `div2 (numeral (2m)) = numeral m`. **La pieza que faltaba de la reparación.** -/
theorem prf_div2_numeral (m : Nat) : Prf (div2 (numeral (2 * m)) =eq numeral m) := by
  have hmul : Prf (mul (numeral m) two =eq numeral (2 * m)) := by
    have h := prf_gnum_mul m 2
    rw [Nat.mul_comm m 2] at h
    exact h
  exact prf_eq_trans (prf_eq_congr_div2 (prf_eq_symm hmul)) (prf_div2_double (numeral m))

/-! ## PARIDAD DE CANTOR — lo que el ensamblaje de `pcc_dot_cons` necesitaba

Para bajar de `pair` a `div2` hace falta `(cons h t)·2 = cpOf h t`, y eso exige que `cpOf h t` sea
**PAR**. Como `cpOf h t = S·σS + 2·σt` con `S = h + σt`, el nudo es que **el producto de dos
consecutivos es par** — que a nivel objeto NO es gratis.

**La salida sin inducción nueva:** case‑split de la paridad de `S` con `ax21`, y en cada rama `ax17`
da la mitad **EXPLÍCITA** (`div2 S`), así que no hace falta ningún existencial.
-/

/-! ### Piezas que faltaban del producto (asociatividad y distributiva por la derecha) -/

/-- `(a·b)·c = a·(b·c)` — instancia de `ax11_mul_assoc`. -/
theorem prf_mul_assoc (a b c : Term) :
    Prf (mul (mul a b) c =eq mul a (mul b c)) := by
  have hh := prf_spec (prf_spec (prf_spec
    (prf_ax (show ax11_mul_assoc ∈ axioms by simp [axioms])) a) b) c
  simp [substFormula, substTerm, substTerms, mul,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

/-- Distributividad por la DERECHA: `(a+b)·c = a·c + b·c`. -/
theorem prf_mul_distrib_right (a b c : Term) :
    Prf (mul (add a b) c =eq add (mul a c) (mul b c)) :=
  prf_eq_trans (prf_mul_comm (add a b) c)
    (prf_eq_trans (prf_mul_distrib c a b)
      (prf_eq_trans (prf_eq_congr_add1 _ (prf_mul_comm c a))
        (prf_eq_congr_add2 _ (prf_mul_comm c b))))

/-- **Mover el `·2` hacia fuera**: `(a·2)·b = (a·b)·2`. -/
theorem prf_swap_mul2 (a b : Term) : Prf (mul (mul a two) b =eq mul (mul a b) two) :=
  prf_eq_trans (prf_mul_assoc a two b)
    (prf_eq_trans (prf_eq_congr_mul2 a (prf_mul_comm two b))
      (prf_eq_symm (prf_mul_assoc a b two)))

/-- Congruencia de `mod2`. -/
theorem prf_eq_congr_mod2 {t₁ t₂ : Term} (h : Prf (t₁ =eq t₂)) :
    Prf (mod2 t₁ =eq mod2 t₂) := by
  let f : Formula := Formula.eq (mod2 (liftTerm 0 t₁)) (mod2 (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (mod2 t₁) (mod2 s) := by
    intro s
    simp only [f, substFormula, mod2, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS t₂) ▸ prf_leibniz_subst (A := f) h ((hS t₁) ▸ prf_refl (mod2 t₁))

/-- Congruencia de `mod2`, en contexto. -/
theorem PrfH_eq_congr_mod2 {Γ : List Formula} {t₁ t₂ : Term} (h : PrfH Γ (t₁ =eq t₂)) :
    PrfH Γ (mod2 t₁ =eq mod2 t₂) := by
  let f : Formula := Formula.eq (mod2 (liftTerm 0 t₁)) (mod2 (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (mod2 t₁) (mod2 s) := by
    intro s
    simp only [f, substFormula, mod2, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS t₂) ▸ PrfH_leibniz_subst (A := f) h ((hS t₁) ▸ prf_to_prfH (prf_refl (mod2 t₁)) Γ)

/-! ### De la paridad de `n` a su mitad EXPLÍCITA (en contexto) -/

/-- `mod2 n = 0 ⟹ (div2 n)·2 = n`. Es `ax17` con el resto anulado. -/
theorem PrfH_double_div2_of_even {Γ : List Formula} {n : Term}
    (h : PrfH Γ (mod2 n =eq zero)) : PrfH Γ (mul (div2 n) two =eq n) :=
  PrfH_eq_trans
    (PrfH_eq_symm (PrfH_eq_trans (PrfH_eq_congr_add2 (mul (div2 n) two) h)
      (prf_to_prfH (prf_add_zero_t (mul (div2 n) two)) _)))
    (prf_to_prfH (prf_div_mod_eq n) _)

/-- `mod2 n = 1 ⟹ σn = (σ(div2 n))·2`: el impar tiene sucesor par. -/
theorem PrfH_succ_double_of_odd {Γ : List Formula} {n : Term}
    (h : PrfH Γ (mod2 n =eq one)) : PrfH Γ (succ n =eq mul (succ (div2 n)) two) := by
  have h1 : PrfH Γ (add (mul (div2 n) two) one =eq n) :=
    PrfH_eq_trans (PrfH_eq_symm (PrfH_eq_congr_add2 (mul (div2 n) two) h))
      (prf_to_prfH (prf_div_mod_eq n) _)
  have h2 : PrfH Γ (succ (add (mul (div2 n) two) one) =eq succ n) := PrfH_eq_congr_succ h1
  have h3 : Prf (mul (succ (div2 n)) two =eq succ (add (mul (div2 n) two) one)) :=
    prf_eq_trans (prf_mul_comm (succ (div2 n)) two)
      (prf_eq_trans (prf_mul_succ two (div2 n))
        (prf_eq_trans (prf_eq_congr_add1 two (prf_mul_comm two (div2 n)))
          (prf_add_succ_t (mul (div2 n) two) one)))
  exact PrfH_eq_symm (PrfH_eq_trans (prf_to_prfH h3 _) h2)

/-! ### El producto de dos CONSECUTIVOS es par -/

/-- **`mod2 (S · σS) = 0`.** Case‑split de la paridad de `S` con `ax21`:
    * `S` par   ⟹ `S = d·2`   ⟹ `S·σS = (d·σS)·2`;
    * `S` impar ⟹ `σS = (σd)·2` ⟹ `S·σS = (S·σd)·2`.
    En ambas ramas la mitad es EXPLÍCITA (`d = div2 S`), sin existenciales. -/
theorem prf_mod2_consec (S : Term) : Prf (mod2 (mul S (succ S)) =eq zero) := by
  refine prf_or_elim (prf_mod2_range S) (prf_deduction ?par) (prf_deduction ?impar)
  · -- `S` PAR: `S = (div2 S)·2`
    have hd : PrfH [mod2 S =eq zero] (mul (div2 S) two =eq S) :=
      PrfH_double_div2_of_even (prfH_hyp_self _)
    -- `S·σS = ((div2 S)·2)·σS = ((div2 S)·σS)·2`
    have hchain : PrfH [mod2 S =eq zero]
        (mul S (succ S) =eq mul (mul (div2 S) (succ S)) two) :=
      PrfH_eq_trans (PrfH_eq_congr_mul1 (succ S) (PrfH_eq_symm hd))
        (prf_to_prfH (prf_swap_mul2 (div2 S) (succ S)) _)
    exact PrfH_eq_trans (PrfH_eq_congr_mod2 hchain)
      (prf_to_prfH (prf_mod2_double (mul (div2 S) (succ S))) _)
  · -- `S` IMPAR: `σS = (σ(div2 S))·2`
    have hd : PrfH [mod2 S =eq one] (succ S =eq mul (succ (div2 S)) two) :=
      PrfH_succ_double_of_odd (prfH_hyp_self _)
    -- `S·σS = S·((σd)·2) = (S·σd)·2`
    have hchain : PrfH [mod2 S =eq one]
        (mul S (succ S) =eq mul (mul S (succ (div2 S))) two) :=
      PrfH_eq_trans (PrfH_eq_congr_mul2 S hd)
        (prf_to_prfH (prf_eq_symm (prf_mul_assoc S (succ (div2 S)) two)) _)
    exact PrfH_eq_trans (PrfH_eq_congr_mod2 hchain)
      (prf_to_prfH (prf_mod2_double (mul S (succ (div2 S)))) _)

/-! ### `cpOf` es par, y por tanto `(cons h t)·2 = cpOf h t` -/

/-- **`cpOf h t` es PAR.** `cpOf = S·σS + 2·σt`: el primer sumando es par por
    `prf_mod2_consec`, el segundo lo es por construcción, y la suma de dos pares es par
    porque se factoriza el `·2` con distributividad. -/
theorem prf_mod2_cpOf (h t : Term) : Prf (mod2 (cpOf h t) =eq zero) := by
  let S : Term := add h (succ t)
  let P : Term := div2 (mul S (succ S))
  -- (1) `S·σS = P·2`
  have h1 : Prf (mul S (succ S) =eq mul P two) :=
    prf_eq_symm (prf_mp (prf_deduction (PrfH_double_div2_of_even (prfH_hyp_self _)))
      (prf_mod2_consec S))
  -- (2) `2·σt = (σt)·2`
  have h2 : Prf (mul two (succ t) =eq mul (succ t) two) := prf_mul_comm two (succ t)
  -- (3) `cpOf = P·2 + (σt)·2 = (P + σt)·2`
  have h3 : Prf (cpOf h t =eq mul (add P (succ t)) two) :=
    prf_eq_trans (prf_eq_trans (prf_eq_congr_add1 _ h1) (prf_eq_congr_add2 _ h2))
      (prf_eq_symm (prf_mul_distrib_right P (succ t) two))
  exact prf_eq_trans (prf_eq_congr_mod2 h3)
    (prf_mod2_double (add P (succ t)))

/-- **LA PIEZA DEL ENSAMBLAJE**: `(cons h t)·2 = cpOf h t`.
    De `prf_cons_div_mod` (que es `ax17` en `cpOf`) anulando el resto con `prf_mod2_cpOf`. -/
theorem prf_cons_double (h t : Term) : Prf (mul (cons h t) two =eq cpOf h t) :=
  prf_eq_trans
    (prf_eq_symm (prf_eq_trans (prf_eq_congr_add2 (mul (cons h t) two) (prf_mod2_cpOf h t))
      (prf_add_zero_t (mul (cons h t) two))))
    (prf_cons_div_mod h t)


end ROBINSON_PlusPlus.Meta.Div2ParityPrf

export ROBINSON_PlusPlus.Meta.Div2ParityPrf (
  prf_mul_distrib PrfH_eq_congr_mul2
  prf_numeral_mul prf_gnum_mul
  prf_mul_two_lt_mono
  prf_mul_two_cancel prf_mod2_double
  prf_eq_congr_div2 prf_div2_double prf_div2_numeral
  prf_mul_assoc prf_mul_distrib_right prf_swap_mul2
  prf_eq_congr_mod2 PrfH_eq_congr_mod2
  PrfH_double_div2_of_even PrfH_succ_double_of_odd
  prf_mod2_consec prf_mod2_cpOf prf_cons_double
)

/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.NatMulPrf
import ROBINSON_PlusPlus.Meta.CantorMonoPrf

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

set_option maxHeartbeats 1000000

namespace ROBINSON_PlusPlus.Meta.Div2ParityPrf

/-!
## META — PARIDAD y `div2`: primer tramo hacia `prf_cons_eval`

Frente **S4** de `PLAN-SORTES.md`: la evaluación provable del emparejamiento de Cantor sobre
numerales, que es lo único que separa a la reparación de la inconsistencia de estar completa para
Gödel I (ver `sondeos/README.md` y la memoria `project-reparacion-via-numeral`).

**La cadena completa** hacia `prf_cons_eval (a b) : Prf (cons ā b̄ =eq numeral (consN a b))`:

| paso | enunciado | estado |
|---|---|---|
| **L1** | `lt x y ⇒ lt (x·2) (y·2)` | ✅ **este módulo** |
| L2 | `(x·2 =eq y·2) ⇒ (x =eq y)` | pendiente |
| L3 | `mod2 (x·2) =eq zero` | pendiente |
| L4 | `div2 (x·2) =eq x` | pendiente |
| L5 | `div2 (numeral (2m)) =eq numeral m` | pendiente |

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

end ROBINSON_PlusPlus.Meta.Div2ParityPrf

export ROBINSON_PlusPlus.Meta.Div2ParityPrf (
  prf_mul_distrib PrfH_eq_congr_mul2
  prf_numeral_mul prf_gnum_mul
  prf_mul_two_lt_mono
)

/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.Div2ParityPrf
import ROBINSON_PlusPlus.Meta.ReprPrf

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.NatArithPrf
open ROBINSON_PlusPlus.Meta.NatOrderPrf
open ROBINSON_PlusPlus.Meta.NatMulPrf
open ROBINSON_PlusPlus.Meta.CantorMonoPrf
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.Div2ParityPrf

set_option maxHeartbeats 1000000

namespace ROBINSON_PlusPlus.Meta.CodeNumeralPrf

/-!
## META — **el código de una fórmula ES un numeral**: `formCode φ =eq numeral (codeNat φ)`

Cierra el frente **S4** de `PLAN-SORTES.md`. Este módulo **descarga la hipótesis `hFN`** que el
piloto del lema diagonal (`sondeos/PilotoDiagonal.lean`) daba por supuesta, y con ella la vía
numeral deja de ser condicional.

**Por qué importa.** La inconsistencia de la teoría objeto viene de que `tcFn` tiene dos lecturas
incompatibles (numeral y sintáctica) porque `⌈φ⌉` se representa como **árbol `cons`**, cuya sintaxis
no se recupera del valor. Con `⌈φ⌉` escrito como **numeral** la ambigüedad desaparece: el numeral es
canónico. Este módulo es el puente entre las dos representaciones.

**La aritmética sale sin división.** `consN` se define con **números triangulares** (`triN`), de modo
que `2 · consN a b = (a+(b+1))·((a+(b+1))+1) + 2·(b+1)` — exactamente `cpOf ā b̄` — es una identidad
`Nat` demostrable **sin** razonar sobre divisibilidad. Eso es lo que hace que
`prf_div2_numeral` (`Div2ParityPrf`) enganche en la forma `2*m` exacta que pide.
-/

/-! ### PARTE A — la aritmética meta, SIN división -/

/-- Números triangulares, definidos por recursión (no por división). -/
def triN : Nat → Nat
  | 0     => 0
  | n + 1 => triN n + (n + 1)

/-- `2·T(n) = n·(n+1)`. Es lo que hace exacta la división por 2 del polinomio de Cantor. -/
theorem two_mul_triN : ∀ n : Nat, 2 * triN n = n * (n + 1)
  | 0     => rfl
  | n + 1 => by
      have ih := two_mul_triN n
      show 2 * (triN n + (n + 1)) = (n + 1) * (n + 1 + 1)
      have hr : (n + 1) * (n + 1 + 1) = n * (n + 1) + (n + 1) + (n + 1) := by
        rw [Nat.succ_mul, Nat.mul_succ]
        generalize n * (n + 1) = A
        omega
      rw [Nat.mul_add, ih, hr]
      generalize n * (n + 1) = A
      omega

/-- Valor de `cons a b`, **sin división**. -/
def consN (a b : Nat) : Nat := triN (a + (b + 1)) + (b + 1)

/-- **LA VERIFICACIÓN**: el polinomio de Cantor de `⟨a,b⟩` es exactamente `2 · consN a b`. -/
theorem two_mul_consN (a b : Nat) :
    2 * consN a b = (a + (b + 1)) * ((a + (b + 1)) + 1) + 2 * (b + 1) := by
  show 2 * (triN (a + (b + 1)) + (b + 1)) = _
  rw [Nat.mul_add, two_mul_triN]

/-! ### PARTE B — evaluación provable -/

/-- Homomorfismo de `+` sobre `Godel.numeral` (no existía; espejo de `prf_gnum_mul`). -/
theorem prf_gnum_add (a b : Nat) : Prf (add (numeral a) (numeral b) =eq numeral (a + b)) := by
  rw [numeral_bridge, numeral_bridge, numeral_bridge]
  exact prf_numeral_add a b

/-- El polinomio de Cantor sobre numerales se evalúa a `numeral (2 · consN a b)`. -/
theorem prf_cpOf_eval (a b : Nat) :
    Prf (cpOf (numeral a) (numeral b) =eq numeral (2 * consN a b)) := by
  -- `s = a + (b+1)`;  `succ (numeral b) = numeral (b+1)` y `two = numeral 2` son DEFEQ
  have hS : Prf (add (numeral a) (succ (numeral b)) =eq numeral (a + (b + 1))) :=
    prf_gnum_add a (b + 1)
  have hSs : Prf (succ (add (numeral a) (succ (numeral b))) =eq numeral (a + (b + 1) + 1)) :=
    prf_eq_congr_succ hS
  have h1 : Prf (mul (add (numeral a) (succ (numeral b)))
                     (succ (add (numeral a) (succ (numeral b))))
              =eq numeral ((a + (b + 1)) * ((a + (b + 1)) + 1))) :=
    prf_eq_trans (prf_eq_congr_mul1 _ hS)
      (prf_eq_trans (prf_eq_congr_mul2 _ hSs) (prf_gnum_mul (a + (b+1)) (a + (b+1) + 1)))
  have h2 : Prf (mul two (succ (numeral b)) =eq numeral (2 * (b + 1))) :=
    prf_gnum_mul 2 (b + 1)
  have hsum : Prf (cpOf (numeral a) (numeral b)
      =eq numeral ((a + (b+1)) * ((a + (b+1)) + 1) + 2 * (b + 1))) :=
    prf_eq_trans (prf_eq_congr_add1 _ h1)
      (prf_eq_trans (prf_eq_congr_add2 _ h2) (prf_gnum_add _ _))
  rw [two_mul_consN]
  exact hsum

/-- **`prf_cons_eval`** — `cons ā b̄ = numeral (consN a b)`. -/
theorem prf_cons_eval (a b : Nat) :
    Prf (cons (numeral a) (numeral b) =eq numeral (consN a b)) :=
  prf_eq_trans (prf_cons_div2 (numeral a) (numeral b))
    (prf_eq_trans (prf_eq_congr_div2 (prf_cpOf_eval a b))
      (prf_div2_numeral (consN a b)))








/-! ### PARTE C — `prf_formCode_numeral` por META-RECURSIÓN

Descarga la `hFN` que el piloto del lema diagonal (`sondeos/PilotoDiagonal.lean`) asumía. -/


open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.ReprPrf

/-- Paso genérico: si los dos hijos ya son numerales, el `cons` se evalúa. -/
theorem prf_cons_eval_of {A B : Term} {a b : Nat}
    (ha : Prf (A =eq numeral a)) (hb : Prf (B =eq numeral b)) :
    Prf (cons A B =eq numeral (consN a b)) :=
  prf_eq_trans (prf_eq_trans (prf_congr_cons_head ha) (prf_congr_cons_tail hb))
    (prf_cons_eval a b)

/-! ### Los códigos, a nivel `Nat` (espejo exacto de `Provability.lean:34-63`) -/

def codeNatChars : List Char → Nat
  | []      => 0
  | c :: cs => consN c.toNat (codeNatChars cs)

def codeNatStr (s : String) : Nat := codeNatChars s.toList

mutual
def codeNatTerm : Term → Nat
  | .var n     => consN 0 (consN n 0)
  | .func s ts => consN 1 (consN (codeNatStr s) (consN (codeNatTerms ts) 0))
def codeNatTerms : List Term → Nat
  | []      => 0
  | t :: ts => consN (codeNatTerm t) (codeNatTerms ts)
end

def codeNat : Formula → Nat
  | .bottom          => consN 2 0
  | .atom p ts       => consN 3 (consN (codeNatStr p) (consN (codeNatTerms ts) 0))
  | .eq t u          => consN 4 (consN (codeNatTerm t) (consN (codeNatTerm u) 0))
  | .impl a b        => consN 5 (consN (codeNat a) (consN (codeNat b) 0))
  | Formula.forall a => consN 6 (consN (codeNat a) 0)
  | .and a b         => consN 7 (consN (codeNat a) (consN (codeNat b) 0))
  | .or a b          => consN 8 (consN (codeNat a) (consN (codeNat b) 0))
  | .ex a            => consN 9 (consN (codeNat a) 0)

/-! ### La transferencia, por recursión estructural -/

theorem prf_charsCode_numeral : ∀ cs : List Char,
    Prf (charsCode cs =eq numeral (codeNatChars cs))
  | []      => prf_refl _
  | c :: cs => prf_cons_eval_of (prf_refl (numeral c.toNat)) (prf_charsCode_numeral cs)

theorem prf_strCode_numeral (s : String) : Prf (strCode s =eq numeral (codeNatStr s)) :=
  prf_charsCode_numeral s.toList

mutual
theorem prf_termCode_numeral : ∀ t : Term, Prf (termCode t =eq numeral (codeNatTerm t))
  | .var n =>
      prf_cons_eval_of (prf_refl (numeral 0))
        (prf_cons_eval_of (prf_refl (numeral n)) (prf_refl nil))
  | .func s ts =>
      prf_cons_eval_of (prf_refl (numeral 1))
        (prf_cons_eval_of (prf_strCode_numeral s)
          (prf_cons_eval_of (prf_termsCode_numeral ts) (prf_refl nil)))
theorem prf_termsCode_numeral : ∀ ts : List Term,
    Prf (termsCode ts =eq numeral (codeNatTerms ts))
  | []      => prf_refl _
  | t :: ts => prf_cons_eval_of (prf_termCode_numeral t) (prf_termsCode_numeral ts)
end

/-- **`prf_formCode_numeral`** — el árbol de código y el numeral de su valor son iguales.
    **Es exactamente la `hFN` del piloto del lema diagonal.** -/
theorem prf_formCode_numeral : ∀ φ : Formula, Prf (formCode φ =eq numeral (codeNat φ))
  | .bottom => prf_cons_eval_of (prf_refl (numeral 2)) (prf_refl nil)
  | .atom p ts =>
      prf_cons_eval_of (prf_refl (numeral 3))
        (prf_cons_eval_of (prf_strCode_numeral p)
          (prf_cons_eval_of (prf_termsCode_numeral ts) (prf_refl nil)))
  | .eq t u =>
      prf_cons_eval_of (prf_refl (numeral 4))
        (prf_cons_eval_of (prf_termCode_numeral t)
          (prf_cons_eval_of (prf_termCode_numeral u) (prf_refl nil)))
  | .impl a b =>
      prf_cons_eval_of (prf_refl (numeral 5))
        (prf_cons_eval_of (prf_formCode_numeral a)
          (prf_cons_eval_of (prf_formCode_numeral b) (prf_refl nil)))
  | Formula.forall a =>
      prf_cons_eval_of (prf_refl (numeral 6))
        (prf_cons_eval_of (prf_formCode_numeral a) (prf_refl nil))
  | .and a b =>
      prf_cons_eval_of (prf_refl (numeral 7))
        (prf_cons_eval_of (prf_formCode_numeral a)
          (prf_cons_eval_of (prf_formCode_numeral b) (prf_refl nil)))
  | .or a b =>
      prf_cons_eval_of (prf_refl (numeral 8))
        (prf_cons_eval_of (prf_formCode_numeral a)
          (prf_cons_eval_of (prf_formCode_numeral b) (prf_refl nil)))
  | .ex a =>
      prf_cons_eval_of (prf_refl (numeral 9))
        (prf_cons_eval_of (prf_formCode_numeral a) (prf_refl nil))






end ROBINSON_PlusPlus.Meta.CodeNumeralPrf

export ROBINSON_PlusPlus.Meta.CodeNumeralPrf (
  triN two_mul_triN consN two_mul_consN
  prf_gnum_add prf_cpOf_eval prf_cons_eval prf_cons_eval_of
  codeNatChars codeNatStr codeNatTerm codeNatTerms codeNat
  prf_charsCode_numeral prf_strCode_numeral
  prf_termCode_numeral prf_termsCode_numeral prf_formCode_numeral
)

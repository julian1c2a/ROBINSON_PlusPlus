/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.CodeNumeralPrf
import ROBINSON_PlusPlus.Meta.CodeNatInjPrf

/-!
# `Meta/ModeloCodigo.lean` — el MODELO ESTÁNDAR de los 142, a nivel `Nat` (ADR‑119/120)

La parte de `Nat` del modelo `MNV V₀` (`Meta/ModeloEstandar.lean`): la raíz `sqrtN`; las LISTAS por la
biyección de Cantor (`cons a b = consN a b = pairN a b + 1`, ADR‑113: todo `n` es una lista, y una sola;
`unpairN`, `decodeL`/`encodeL`, `concatN`, `memN`, `prodpN`); los accesores (`carN`, `cdrN`, `nthN`, `lenN`) con
`nthN_lt` —un componente es MENOR que su código—, que es lo que deja recurrir; y las funciones de codificación:
`substtcN`/`substtscN`, `liftcN`/`liftscN`, `substfcN`, `liftfcN` (por la etiqueta de su argumento, una ecuación
por constructor), `tcFnN`, `vpfN` (con `stepT`, la conclusión de cada etiqueta), `runFnN`, `premsOfN`, `allInN`,
`chainOkN`, las guardas `hasWitN`/`hasWitFN` y `lineWFT`, las 21 RHS de `ax_lineWF_K` traducidas (generadas del
fuente y parametrizadas en `V` a mano). `validProofFn`, `runFn` y `chainOk` recurren sobre `decodeL`; `tcFn`, sobre el
número.

`V₀` es el valor del lado derecho del ancla `ax_axiomsCodeT_def`. ⛔ Nada lo evalúa: dentro lleva el numeral
astronómico del ancla, PLEGADO (`codeNat (psiD axiomsBase)`), y todo lo que lo toca es PARAMÉTRICO en `V`
(`lineWFT V`, `chainOkN V`) y lo recibe por instanciación (ADR‑119 §3).

Sin semántica: no importa `FOL.Semantics`. Pasó por `sondeos/ModeloNat.lean` (ADR‑119), que se conserva.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Meta.ModeloCodigo

/-! ## §1 · La raíz entera sobre `Nat`

Estilo `triN`: **recursión, sin división**, para que `omega` trate los productos como átomos. -/

def sqrtN : Nat → Nat
  | 0 => 0
  | n + 1 => if (sqrtN n + 1) * (sqrtN n + 1) ≤ n + 1 then sqrtN n + 1 else sqrtN n

/-- La única pieza no lineal.
    ⚠️ El sucesor va como `k+1+1` y **NO** como `k+2`: para `omega` el producto es un **ÁTOMO**,
    y `(k+2)*(k+2)` y `(k+1+1)*(k+1+1)` son átomos **distintos**. Con `k+2` no cierra. -/
theorem sq_lt_sq_succ (k : Nat) : (k + 1) * (k + 1) < (k + 1 + 1) * (k + 1 + 1) := by
  have h1 : (k + 1 + 1) * (k + 1 + 1) = (k + 1) * (k + 1) + 2 * (k + 1) + 1 := by
    rw [Nat.succ_mul, Nat.mul_succ]
    generalize (k + 1) * (k + 1) = A
    omega
  omega

/-- `ax14_sqrt_le` en el modelo: `sq (√x) ≤ x`. -/
theorem sqrtN_le : ∀ n : Nat, sqrtN n * sqrtN n ≤ n
  | 0 => by simp [sqrtN]
  | n + 1 => by
      have ih := sqrtN_le n
      simp only [sqrtN]
      by_cases h : (sqrtN n + 1) * (sqrtN n + 1) ≤ n + 1
      · rw [if_pos h]; exact h
      · rw [if_neg h]; omega

/-- `ax15_lt_succ_sqrt` en el modelo: `x < sq (σ (√x))`. -/
theorem lt_sq_succ_sqrtN : ∀ n : Nat, n < (sqrtN n + 1) * (sqrtN n + 1)
  | 0 => by simp [sqrtN]
  | n + 1 => by
      have ih := lt_sq_succ_sqrtN n
      have ih2 := sqrtN_le n
      simp only [sqrtN]
      by_cases h : (sqrtN n + 1) * (sqrtN n + 1) ≤ n + 1
      · rw [if_pos h]
        have hlt := sq_lt_sq_succ (sqrtN n)
        omega
      · rw [if_neg h]; exact Nat.lt_of_not_le h

/-! ## §1bis · Las LISTAS sobre `Nat` (2026‑10‑05)

`nil = 0` y `cons a b = consN a b = pairN a b + 1` (ADR‑113): **toda** `n` es una lista, y una sola —`pairN` es
la biyección de Cantor `ℕ² → ℕ`—. `unpairN` la invierte por recursión (recorre las diagonales en el orden de
`pairN`), `decodeL`/`encodeL` son la biyección `ℕ ≅ List ℕ`, y `concatN`, `memN` y `prodpN` son las operaciones
de `List` vistas a través de ella. Sin `Classical.choice`: `[propext, Quot.sound]`. -/

section Listas
open FOL
open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.CodeNumeralPrf ROBINSON_PlusPlus.Meta.CodeNatInjPrf

/-! ### Listas: la biyección de Cantor `ℕ ≅ List ℕ` -/

def unpairN : Nat → Nat × Nat
  | 0 => (0, 0)
  | n + 1 =>
    match unpairN n with
    | (0, b) => (b + 1, 0)
    | (a + 1, b) => (a, b + 1)

theorem pairN_unpairN : ∀ n : Nat, pairN (unpairN n).1 (unpairN n).2 = n
  | 0 => rfl
  | n + 1 => by
      have ih := pairN_unpairN n
      simp only [unpairN]
      split
      · rename_i b h
        rw [h] at ih
        simp only [pairN] at ih ⊢
        rw [Nat.zero_add] at ih
        show triN (b + 1 + 0) + 0 = n + 1
        rw [Nat.add_zero, Nat.add_zero, triN_succ]
        omega
      · rename_i a b h
        rw [h] at ih
        have ih' : triN (a + 1 + b) + b = n := ih
        show triN (a + (b + 1)) + (b + 1) = n + 1
        have e : a + (b + 1) = a + 1 + b := by omega
        rw [e]
        omega

theorem pairN_inj {a b a' b' : Nat} (h : pairN a b = pairN a' b') : And (a = a') (b = b') :=
  consN_inj (show consN a b = consN a' b' by simp only [consN, pairN] at h ⊢; omega)

theorem unpairN_pairN (a b : Nat) : unpairN (pairN a b) = (a, b) := by
  have h := pairN_unpairN (pairN a b)
  obtain ⟨h1, h2⟩ := pairN_inj h
  exact Prod.ext h1 h2

theorem le_triN : ∀ s : Nat, s < triN s + 1
  | 0 => by decide
  | s + 1 => by have := le_triN s; rw [triN_succ]; omega

theorem snd_le_pairN (a b : Nat) : b < pairN a b + 1 := by
  simp only [pairN]; omega

theorem fst_le_pairN (a b : Nat) : a < pairN a b + 1 := by
  have := le_triN (a + b)
  simp only [pairN]; omega

theorem unpairN_snd_lt (n : Nat) : (unpairN n).2 < n + 1 := by
  have h := pairN_unpairN n
  have := snd_le_pairN (unpairN n).1 (unpairN n).2
  omega

theorem unpairN_fst_lt (n : Nat) : (unpairN n).1 < n + 1 := by
  have h := pairN_unpairN n
  have := fst_le_pairN (unpairN n).1 (unpairN n).2
  omega

def decodeL : Nat → List Nat
  | 0 => []
  | n + 1 => (unpairN n).1 :: decodeL (unpairN n).2
termination_by n => n
decreasing_by exact unpairN_snd_lt n

def encodeL : List Nat → Nat
  | [] => 0
  | a :: l => consN a (encodeL l)

theorem consN_eq (a b : Nat) : consN a b = pairN a b + 1 := rfl

theorem decodeL_zero : decodeL 0 = [] := by rw [decodeL]

theorem decodeL_consN (a b : Nat) : decodeL (consN a b) = a :: decodeL b := by
  rw [consN_eq, decodeL, unpairN_pairN]

theorem decodeL_encodeL : ∀ l : List Nat, decodeL (encodeL l) = l
  | [] => decodeL_zero
  | a :: l => by rw [encodeL, decodeL_consN, decodeL_encodeL l]

theorem encodeL_decodeL (n : Nat) : encodeL (decodeL n) = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => rw [decodeL_zero]; rfl
    | succ m =>
      rw [decodeL, encodeL, ih _ (unpairN_snd_lt m), consN_eq, pairN_unpairN]

def concatN (a b : Nat) : Nat := encodeL (decodeL a ++ decodeL b)
def memN (x l : Nat) : Prop := x ∈ decodeL l

theorem concatN_zero (b : Nat) : concatN 0 b = b := by
  rw [concatN, decodeL_zero, List.nil_append, encodeL_decodeL]

theorem concatN_consN (a b c : Nat) : concatN (consN a b) c = consN a (concatN b c) := by
  rw [concatN, decodeL_consN, List.cons_append, encodeL, concatN]

theorem memN_zero (x : Nat) : ¬ memN x 0 := by
  rw [memN, decodeL_zero]; exact List.not_mem_nil

theorem memN_consN (x a b : Nat) : memN x (consN a b) ↔ Or (x = a) (memN x b) := by
  rw [memN, decodeL_consN, List.mem_cons, memN]

/-! ### Accesores: `carc`, `cdrc`, `nthc`, `lenc` -/

def carN : Nat → Nat
  | 0 => 0
  | m + 1 => (unpairN m).1

def cdrN : Nat → Nat
  | 0 => 0
  | m + 1 => (unpairN m).2

/-- `nthc l i`: el `i`‑ésimo, por la cola (estructural en `i`). Fuera de rango, `0`. -/
def nthN (l : Nat) : Nat → Nat
  | 0 => carN l
  | i + 1 => nthN (cdrN l) i

def lenN (l : Nat) : Nat := (decodeL l).length

theorem carN_consN (a b : Nat) : carN (consN a b) = a := by
  rw [consN_eq, carN, unpairN_pairN]

theorem cdrN_consN (a b : Nat) : cdrN (consN a b) = b := by
  rw [consN_eq, cdrN, unpairN_pairN]

theorem nthN_cz (a b : Nat) : nthN (consN a b) 0 = a := carN_consN a b

theorem nthN_cs (a b i : Nat) : nthN (consN a b) (i + 1) = nthN b i := by
  rw [nthN, cdrN_consN]

theorem lenN_zero : lenN 0 = 0 := by rw [lenN, decodeL_zero]; rfl

theorem lenN_consN (a b : Nat) : lenN (consN a b) = lenN b + 1 := by
  rw [lenN, decodeL_consN, List.length_cons, lenN]

theorem carN_lt {l : Nat} (h : ¬ l = 0) : carN l < l := by
  cases l with
  | zero => exact absurd rfl h
  | succ m => exact unpairN_fst_lt m

theorem cdrN_lt {l : Nat} (h : ¬ l = 0) : cdrN l < l := by
  cases l with
  | zero => exact absurd rfl h
  | succ m => exact unpairN_snd_lt m

theorem nthN_zero_l : ∀ i : Nat, nthN 0 i = 0
  | 0 => rfl
  | i + 1 => nthN_zero_l i

theorem nthN_lt : ∀ (i : Nat) {l : Nat}, ¬ l = 0 → nthN l i < l
  | 0, _, h => carN_lt h
  | i + 1, l, h => by
      show nthN (cdrN l) i < l
      by_cases hc : cdrN l = 0
      · rw [hc, nthN_zero_l]; exact Nat.pos_of_ne_zero h
      · exact Nat.lt_trans (nthN_lt i hc) (cdrN_lt h)

theorem consN_car_cdr {l : Nat} (h : ¬ l = 0) : consN (carN l) (cdrN l) = l := by
  cases l with
  | zero => exact absurd rfl h
  | succ m => rw [consN_eq, carN, cdrN, pairN_unpairN]

/-! ### La sustitución y el lift sobre códigos de TÉRMINO -/

mutual
def substtcN (k s c : Nat) : Nat :=
  if h : c = 0 then 0
  else if nthN c 0 = 0 then
    (if k = nthN c 1 then s
     else if k < nthN c 1 then consN 0 (consN (nthN c 1 - 1) 0)
     else consN 0 (consN (nthN c 1) 0))
  else if nthN c 0 = 1 then consN 1 (consN (nthN c 1) (consN (substtscN k s (nthN c 2)) 0))
  else 0
termination_by c
decreasing_by exact nthN_lt 2 h

def substtscN (k s l : Nat) : Nat :=
  if _h : l = 0 then 0
  else consN (substtcN k s (carN l)) (substtscN k s (cdrN l))
termination_by l
decreasing_by
  · exact carN_lt _h
  · exact cdrN_lt _h
end

mutual
def liftcN (c t : Nat) : Nat :=
  if h : t = 0 then 0
  else if nthN t 0 = 0 then
    (if nthN t 1 < c then consN 0 (consN (nthN t 1) 0) else consN 0 (consN (nthN t 1 + 1) 0))
  else if nthN t 0 = 1 then consN 1 (consN (nthN t 1) (consN (liftscN c (nthN t 2)) 0))
  else 0
termination_by t
decreasing_by exact nthN_lt 2 h

def liftscN (c l : Nat) : Nat :=
  if _h : l = 0 then 0
  else consN (liftcN c (carN l)) (liftscN c (cdrN l))
termination_by l
decreasing_by
  · exact carN_lt _h
  · exact cdrN_lt _h
end

theorem substtcN_var (k s n : Nat) : substtcN k s (consN 0 (consN n 0)) =
    if k = n then s else if k < n then consN 0 (consN (n - 1) 0) else consN 0 (consN n 0) := by
  rw [substtcN, dif_neg (consN_ne_zero _ _), nthN_cz, if_pos rfl, nthN_cs, nthN_cz]

theorem substtcN_func (k s a b : Nat) : substtcN k s (consN 1 (consN a (consN b 0))) =
    consN 1 (consN a (consN (substtscN k s b) 0)) := by
  rw [substtcN, dif_neg (consN_ne_zero _ _), nthN_cz, if_neg (by decide), if_pos rfl,
    nthN_cs, nthN_cz, nthN_cs, nthN_cs, nthN_cz]

theorem substtscN_zero (k s : Nat) : substtscN k s 0 = 0 := by
  rw [substtscN, dif_pos rfl]

theorem substtscN_consN (k s a b : Nat) : substtscN k s (consN a b) =
    consN (substtcN k s a) (substtscN k s b) := by
  rw [substtscN, dif_neg (consN_ne_zero _ _), carN_consN, cdrN_consN]

theorem liftcN_var (c n : Nat) : liftcN c (consN 0 (consN n 0)) =
    if n < c then consN 0 (consN n 0) else consN 0 (consN (n + 1) 0) := by
  rw [liftcN, dif_neg (consN_ne_zero _ _), nthN_cz, if_pos rfl, nthN_cs, nthN_cz]

theorem liftcN_func (c a b : Nat) : liftcN c (consN 1 (consN a (consN b 0))) =
    consN 1 (consN a (consN (liftscN c b) 0)) := by
  rw [liftcN, dif_neg (consN_ne_zero _ _), nthN_cz, if_neg (by decide), if_pos rfl,
    nthN_cs, nthN_cz, nthN_cs, nthN_cs, nthN_cz]

theorem liftscN_zero (c : Nat) : liftscN c 0 = 0 := by
  rw [liftscN, dif_pos rfl]

theorem liftscN_consN (c a b : Nat) : liftscN c (consN a b) = consN (liftcN c a) (liftscN c b) := by
  rw [liftscN, dif_neg (consN_ne_zero _ _), carN_consN, cdrN_consN]

/-! ### La sustitución y el lift sobre códigos de FÓRMULA -/

def substfcN (v t f : Nat) : Nat :=
  if h : f = 0 then 0
  else if nthN f 0 = 2 then consN 2 0
  else if nthN f 0 = 3 then consN 3 (consN (nthN f 1) (consN (substtscN v t (nthN f 2)) 0))
  else if nthN f 0 = 4 then consN 4 (consN (substtcN v t (nthN f 1)) (consN (substtcN v t (nthN f 2)) 0))
  else if nthN f 0 = 5 then consN 5 (consN (substfcN v t (nthN f 1)) (consN (substfcN v t (nthN f 2)) 0))
  else if nthN f 0 = 6 then consN 6 (consN (substfcN (v + 1) (liftcN 0 t) (nthN f 1)) 0)
  else if nthN f 0 = 7 then consN 7 (consN (substfcN v t (nthN f 1)) (consN (substfcN v t (nthN f 2)) 0))
  else if nthN f 0 = 8 then consN 8 (consN (substfcN v t (nthN f 1)) (consN (substfcN v t (nthN f 2)) 0))
  else if nthN f 0 = 9 then consN 9 (consN (substfcN (v + 1) (liftcN 0 t) (nthN f 1)) 0)
  else 0
termination_by f
decreasing_by all_goals exact nthN_lt _ h

def liftfcN (c f : Nat) : Nat :=
  if h : f = 0 then 0
  else if nthN f 0 = 2 then consN 2 0
  else if nthN f 0 = 3 then consN 3 (consN (nthN f 1) (consN (liftscN c (nthN f 2)) 0))
  else if nthN f 0 = 4 then consN 4 (consN (liftcN c (nthN f 1)) (consN (liftcN c (nthN f 2)) 0))
  else if nthN f 0 = 5 then consN 5 (consN (liftfcN c (nthN f 1)) (consN (liftfcN c (nthN f 2)) 0))
  else if nthN f 0 = 6 then consN 6 (consN (liftfcN (c + 1) (nthN f 1)) 0)
  else if nthN f 0 = 7 then consN 7 (consN (liftfcN c (nthN f 1)) (consN (liftfcN c (nthN f 2)) 0))
  else if nthN f 0 = 8 then consN 8 (consN (liftfcN c (nthN f 1)) (consN (liftfcN c (nthN f 2)) 0))
  else if nthN f 0 = 9 then consN 9 (consN (liftfcN (c + 1) (nthN f 1)) 0)
  else 0
termination_by f
decreasing_by all_goals exact nthN_lt _ h

/-- Las ecuaciones, una por constructor: `simp only` con los accesores sobre `consN` y la
    aritmética de literales; nada recursivo se despliega más de un nivel. -/
theorem substfcN_bot (v t : Nat) : substfcN v t (consN 2 0) = consN 2 0 := by
  rw [substfcN]; simp only [consN_ne_zero, nthN_cz, dite_false, ite_true]

theorem substfcN_atom (v t a b : Nat) : substfcN v t (consN 3 (consN a (consN b 0))) =
    consN 3 (consN a (consN (substtscN v t b) 0)) := by
  rw [substfcN]; simp only [consN_ne_zero, nthN_cz, nthN_cs, dite_false]; rfl

theorem substfcN_eq (v t a b : Nat) : substfcN v t (consN 4 (consN a (consN b 0))) =
    consN 4 (consN (substtcN v t a) (consN (substtcN v t b) 0)) := by
  rw [substfcN]; simp only [consN_ne_zero, nthN_cz, nthN_cs, dite_false]; rfl

theorem substfcN_impl (v t a b : Nat) : substfcN v t (consN 5 (consN a (consN b 0))) =
    consN 5 (consN (substfcN v t a) (consN (substfcN v t b) 0)) := by
  rw [substfcN]; simp only [consN_ne_zero, nthN_cz, nthN_cs, dite_false]; rfl

theorem substfcN_forall (v t a : Nat) : substfcN v t (consN 6 (consN a 0)) =
    consN 6 (consN (substfcN (v + 1) (liftcN 0 t) a) 0) := by
  rw [substfcN]; simp only [consN_ne_zero, nthN_cz, nthN_cs, dite_false]; rfl

theorem substfcN_and (v t a b : Nat) : substfcN v t (consN 7 (consN a (consN b 0))) =
    consN 7 (consN (substfcN v t a) (consN (substfcN v t b) 0)) := by
  rw [substfcN]; simp only [consN_ne_zero, nthN_cz, nthN_cs, dite_false]; rfl

theorem substfcN_or (v t a b : Nat) : substfcN v t (consN 8 (consN a (consN b 0))) =
    consN 8 (consN (substfcN v t a) (consN (substfcN v t b) 0)) := by
  rw [substfcN]; simp only [consN_ne_zero, nthN_cz, nthN_cs, dite_false]; rfl

theorem substfcN_ex (v t a : Nat) : substfcN v t (consN 9 (consN a 0)) =
    consN 9 (consN (substfcN (v + 1) (liftcN 0 t) a) 0) := by
  rw [substfcN]; simp only [consN_ne_zero, nthN_cz, nthN_cs, dite_false]; rfl

theorem liftfcN_bot (c : Nat) : liftfcN c (consN 2 0) = consN 2 0 := by
  rw [liftfcN]; simp only [consN_ne_zero, nthN_cz, dite_false, ite_true]

theorem liftfcN_atom (c a b : Nat) : liftfcN c (consN 3 (consN a (consN b 0))) =
    consN 3 (consN a (consN (liftscN c b) 0)) := by
  rw [liftfcN]; simp only [consN_ne_zero, nthN_cz, nthN_cs, dite_false]; rfl

theorem liftfcN_eq (c a b : Nat) : liftfcN c (consN 4 (consN a (consN b 0))) =
    consN 4 (consN (liftcN c a) (consN (liftcN c b) 0)) := by
  rw [liftfcN]; simp only [consN_ne_zero, nthN_cz, nthN_cs, dite_false]; rfl

theorem liftfcN_impl (c a b : Nat) : liftfcN c (consN 5 (consN a (consN b 0))) =
    consN 5 (consN (liftfcN c a) (consN (liftfcN c b) 0)) := by
  rw [liftfcN]; simp only [consN_ne_zero, nthN_cz, nthN_cs, dite_false]; rfl

theorem liftfcN_forall (c a : Nat) : liftfcN c (consN 6 (consN a 0)) =
    consN 6 (consN (liftfcN (c + 1) a) 0) := by
  rw [liftfcN]; simp only [consN_ne_zero, nthN_cz, nthN_cs, dite_false]; rfl

theorem liftfcN_and (c a b : Nat) : liftfcN c (consN 7 (consN a (consN b 0))) =
    consN 7 (consN (liftfcN c a) (consN (liftfcN c b) 0)) := by
  rw [liftfcN]; simp only [consN_ne_zero, nthN_cz, nthN_cs, dite_false]; rfl

theorem liftfcN_or (c a b : Nat) : liftfcN c (consN 8 (consN a (consN b 0))) =
    consN 8 (consN (liftfcN c a) (consN (liftfcN c b) 0)) := by
  rw [liftfcN]; simp only [consN_ne_zero, nthN_cz, nthN_cs, dite_false]; rfl

theorem liftfcN_ex (c a : Nat) : liftfcN c (consN 9 (consN a 0)) =
    consN 9 (consN (liftfcN (c + 1) a) 0) := by
  rw [liftfcN]; simp only [consN_ne_zero, nthN_cz, nthN_cs, dite_false]; rfl


theorem concatN_assoc (a b c : Nat) : concatN (concatN a b) c = concatN a (concatN b c) := by
  simp only [concatN, decodeL_encodeL, List.append_assoc]

theorem memN_concatN (x a b : Nat) : memN x (concatN a b) ↔ Or (memN x a) (memN x b) := by
  rw [memN, concatN, decodeL_encodeL, List.mem_append, memN, memN]

def prodpN (l : Nat) : Nat :=
  ((decodeL l).map (fun h => (unpairN h).1 ^ (unpairN h).2)).foldr (· * ·) 1

theorem prodpN_zero : prodpN 0 = 1 := by
  rw [prodpN, decodeL_zero]; rfl

theorem prodpN_consN_pairN (p e t : Nat) : prodpN (consN (pairN p e) t) = p ^ e * prodpN t := by
  rw [prodpN, decodeL_consN, List.map_cons, List.foldr_cons, unpairN_pairN, prodpN]

/-! ### Los constructores de código, como valores -/

abbrev botcN : Nat := consN 2 0
abbrev eqcN (a b : Nat) : Nat := consN 4 (consN a (consN b 0))
abbrev implcN (a b : Nat) : Nat := consN 5 (consN a (consN b 0))
abbrev forallcN (a : Nat) : Nat := consN 6 (consN a 0)
abbrev andcN (a b : Nat) : Nat := consN 7 (consN a (consN b 0))
abbrev orcN (a b : Nat) : Nat := consN 8 (consN a (consN b 0))
abbrev excN (a : Nat) : Nat := consN 9 (consN a 0)

/-- Los códigos CERRADOS que incrustan `ax_vpf_ind`/`_listInd` y `ax_lineWF_ind`/`_listInd`: su valor se nombra,
    nunca se calcula (`codeNatTerm` de un símbolo `String`). -/
def TC0 : Nat := codeNatTerm zero
def TCS : Nat := codeNatTerm (succ (.var 0))
def TNIL : Nat := codeNatTerm nil
def TCONS : Nat := codeNatTerm (cons (.var 1) (.var 0))

/-! ### `tcFn`: el código del numeral, por recursión estructural -/

def tcFnN : Nat → Nat
  | 0 => consN 1 (consN (codeNatStr zero_sym) (consN 0 0))
  | n + 1 => consN 1 (consN (codeNatStr succ_sym) (consN (consN (tcFnN n) 0) 0))

/-! ### `validProofFn`: la conclusión de una línea `⟨K, a, b, d⟩` según su etiqueta -/

def stepT : Nat → Nat → Nat → Nat → Nat
  | 0, a, b, _ => implcN a (implcN b a)
  | 1, a, b, d => implcN (implcN a (implcN b d)) (implcN (implcN a b) (implcN a d))
  | 2, a, b, _ => implcN a (implcN b (andcN a b))
  | 3, a, b, _ => implcN (andcN a b) a
  | 4, a, b, _ => implcN (andcN a b) b
  | 5, a, b, _ => implcN a (orcN a b)
  | 6, a, b, _ => implcN b (orcN a b)
  | 7, a, b, d => implcN (orcN a b) (implcN (implcN a d) (implcN (implcN b d) d))
  | 8, a, _, _ => implcN botcN a
  | 9, a, b, _ => implcN (forallcN a) (substfcN 0 b a)
  | 10, a, b, _ => implcN (substfcN 0 b a) (excN a)
  | 11, a, b, _ => implcN (forallcN (implcN a (liftfcN 0 b))) (implcN (excN a) b)
  | 12, a, _, _ => eqcN a a
  | 13, a, b, d => implcN (eqcN b d) (implcN (substfcN 0 b a) (substfcN 0 d a))
  | 14, a, _, _ => implcN (implcN (implcN a botcN) botcN) a
  | 15, a, _, _ => a
  | 16, a, _, _ => a
  | 17, a, _, _ => forallcN a
  | 18, a, _, _ => implcN (substfcN 0 TC0 a)
      (implcN (forallcN (implcN a (substfcN 0 TCS (liftfcN 1 a)))) (forallcN a))
  | 19, a, b, _ => implcN (forallcN (implcN (liftfcN 0 a) b)) (implcN a (forallcN b))
  | 20, a, _, _ => implcN (substfcN 0 TNIL a)
      (implcN (forallcN (forallcN (implcN (liftfcN 1 a) (substfcN 0 TCONS (liftfcN 2 (liftfcN 1 a))))))
        (forallcN a))
  | _, _, _, _ => 0

def stepN (x : Nat) : Nat := stepT (nthN x 0) (nthN x 1) (nthN x 2) (nthN x 3)

def vpfL : Nat → List Nat → Nat
  | c, [] => c
  | c, x :: r => vpfL (concatN c (consN (stepN x) 0)) r

def vpfN (c r : Nat) : Nat := vpfL c (decodeL r)

theorem vpfN_zero (c : Nat) : vpfN c 0 = c := by rw [vpfN, decodeL_zero]; rfl

theorem vpfN_consN (c x r : Nat) : vpfN c (consN x r) = vpfN (concatN c (consN (stepN x) 0)) r := by
  rw [vpfN, decodeL_consN]; rfl

/-! ### `runFn`, `premsOf`, `allIn`, `chainOk` -/

def runFnL : Nat → List Nat → Nat
  | c, [] => c
  | c, x :: r => runFnL (concatN c (consN (carN x) 0)) r

def runFnN (c r : Nat) : Nat := runFnL c (decodeL r)

theorem runFnN_zero (c : Nat) : runFnN c 0 = c := by rw [runFnN, decodeL_zero]; rfl

theorem runFnN_consN (c x r : Nat) : runFnN c (consN x r) = runFnN (concatN c (consN (carN x) 0)) r := by
  rw [runFnN, decodeL_consN]; rfl

/-- Las premisas de una línea `⟨concl, K, args…⟩`: `mp` (16) y `gen` (17); las demás, ninguna. -/
def premsOfN (x : Nat) : Nat :=
  if nthN x 1 = 16 then consN (implcN (nthN x 2) (nthN x 0)) (consN (nthN x 2) 0)
  else if nthN x 1 = 17 then consN (nthN x 2) 0
  else 0

def allInN (c L : Nat) : Prop := ∀ y, memN y L → memN y c

theorem allInN_zero (c : Nat) : allInN c 0 := fun y h => absurd h (memN_zero y)

theorem allInN_consN (c a t : Nat) : allInN c (consN a t) ↔ And (memN a c) (allInN c t) := by
  constructor
  · intro h
    exact ⟨h a ((memN_consN a a t).mpr (Or.inl rfl)), fun y hy => h y ((memN_consN y a t).mpr (Or.inr hy))⟩
  · intro h y hy
    cases (memN_consN y a t).mp hy with
    | inl e => rw [e]; exact h.1
    | inr h' => exact h.2 y h'

/-! ### Las guardas `hasWit`/`hasWitF`, como `Prop` sobre `Nat` (espejo de `Minimal/Axioms.lean:1196-1277`) -/

def shapeUnN (X k : Nat) : Prop := X = consN k (consN (nthN X 1) 0)
def shapeBinN (X k : Nat) : Prop := X = consN k (consN (nthN X 1) (consN (nthN X 2) 0))
def argsInN (wT Y : Nat) : Prop := ∀ i, i < lenN Y → memN (nthN Y i) wT
def isTermCodeE1N (wT X : Nat) : Prop := Or (shapeUnN X 0) (And (shapeBinN X 1) (argsInN wT (nthN X 2)))
def wfAll1N (w : Nat) : Prop := ∀ i, i < lenN w → isTermCodeE1N w (nthN w i)
def hasWitN (c : Nat) : Prop := ∃ w, And (wfAll1N w) (memN c w)
def clBotN (X : Nat) : Prop := X = consN 2 0
def clAtomN (wT X : Nat) : Prop := And (shapeBinN X 3) (argsInN wT (nthN X 2))
def clEqN (wT X : Nat) : Prop := And (shapeBinN X 4) (And (memN (nthN X 1) wT) (memN (nthN X 2) wT))
def clBinN (wF X k : Nat) : Prop := And (shapeBinN X k) (And (memN (nthN X 1) wF) (memN (nthN X 2) wF))
def clUnN (wF X k : Nat) : Prop := And (shapeUnN X k) (memN (nthN X 1) wF)
def isFormCodeE2N (wF wT X : Nat) : Prop :=
  Or (clBotN X) (Or (clAtomN wT X) (Or (clEqN wT X) (Or (clBinN wF X 5) (Or (clUnN wF X 6)
    (Or (clBinN wF X 7) (Or (clBinN wF X 8) (clUnN wF X 9)))))))
def wfAllFN (wF wT : Nat) : Prop := ∀ i, i < lenN wF → isFormCodeE2N wF wT (nthN wF i)
def hasWitFN (c : Nat) : Prop := ∃ wF, ∃ wT, And (And (wfAll1N wT) (wfAllFN wF wT)) (memN c wF)

/-! ### El valor del ANCLA: el de su lado derecho, que no nombra `axiomsCodeT`

⛔ Ni se evalúa ni se despliega: es una expresión de `Nat` con el código de los 141 de la base y el de `δ`,
y las pruebas sólo la mueven por `rw` con lemas ∀ (el numeral astronómico del ancla vive aquí dentro, como
`codeNat (psiD axiomsBase)`, PLEGADO). -/

def codeNatList : List Formula → Nat
  | [] => 0
  | f :: fs => consN (codeNat f) (codeNatList fs)

def V₀ : Nat :=
  concatN (codeNatList axiomsBase)
    (consN (substfcN 0 (tcFnN (codeNat (psiD axiomsBase))) (codeNat (psiD axiomsBase))) 0)

/-! ### `lineWF`, por etiqueta -/

/-- Las 21 RHS de `ax_lineWF_K`, traducidas a `Prop` sobre `Nat`: generadas del fuente por un script (en el
    scratchpad de la sesión del 2026‑10‑05, no versionado) y después parametrizadas en `V` a mano (la firma y
    el caso `thy`). La correspondencia la comprueba el núcleo: `v_lineWF_*` cierra por `Iff.rfl`. -/
def lineWFT (V : Nat) : Nat → Nat → Prop
  | 0, x => And (lenN x = 4)
      ((carN x) = implcN (nthN x (2))
        (implcN (nthN x (3)) (nthN x (2))))   -- p1
  | 1, x => And (lenN x = 5) ((carN x) = implcN (implcN (nthN x (2)) (implcN (nthN x (3)) (nthN x (4)))) (implcN (implcN (nthN x (2)) (nthN x (3))) (implcN (nthN x (2)) (nthN x (4)))))   -- p2
  | 2, x => And (lenN x = 4) ((carN x) = implcN (nthN x (2)) (implcN (nthN x (3)) (andcN (nthN x (2)) (nthN x (3)))))   -- c1
  | 3, x => And (lenN x = 4) ((carN x) = implcN (andcN (nthN x (2)) (nthN x (3))) (nthN x (2)))   -- c2
  | 4, x => And (lenN x = 4) ((carN x) = implcN (andcN (nthN x (2)) (nthN x (3))) (nthN x (3)))   -- c3
  | 5, x => And (lenN x = 4) ((carN x) = implcN (nthN x (2)) (orcN (nthN x (2)) (nthN x (3))))   -- j1
  | 6, x => And (lenN x = 4) ((carN x) = implcN (nthN x (3)) (orcN (nthN x (2)) (nthN x (3))))   -- j2
  | 7, x => And (lenN x = 5) ((carN x) = implcN (orcN (nthN x (2)) (nthN x (3))) (implcN (implcN (nthN x (2)) (nthN x (4))) (implcN (implcN (nthN x (3)) (nthN x (4))) (nthN x (4)))))   -- j3
  | 8, x => And (lenN x = 3) ((carN x) = implcN (botcN) (nthN x (2)))   -- efq
  | 9, x => And (lenN x = 4) (And (hasWitFN (nthN x (2))) (And (hasWitN (nthN x (3))) ((carN x) = implcN (forallcN (nthN x (2))) (substfcN 0 (nthN x (3)) (nthN x (2))))))   -- q1
  | 10, x => And (lenN x = 4) (And (hasWitFN (nthN x (2))) (And (hasWitN (nthN x (3))) ((carN x) = implcN (substfcN 0 (nthN x (3)) (nthN x (2))) (excN (nthN x (2))))))   -- q2
  | 11, x => And (lenN x = 4) (And (hasWitFN (nthN x (3))) ((carN x) = implcN (forallcN (implcN (nthN x (2)) (liftfcN 0 (nthN x (3))))) (implcN (excN (nthN x (2))) (nthN x (3)))))   -- q3
  | 12, x => And (lenN x = 3)
      ((carN x) = eqcN (nthN x (2)) (nthN x (2)))   -- eqrefl
  | 13, x => And (lenN x = 5) (And (hasWitFN (nthN x (2))) (And (hasWitN (nthN x (3))) (And (hasWitN (nthN x (4))) ((carN x) = implcN (eqcN (nthN x (3)) (nthN x (4))) (implcN (substfcN 0 (nthN x (3)) (nthN x (2))) (substfcN 0 (nthN x (4)) (nthN x (2))))))))   -- leibniz
  | 14, x => And (lenN x = 3) ((carN x) = implcN (implcN (implcN (nthN x (2)) (botcN)) (botcN)) (nthN x (2)))   -- p3
  | 15, x => And (lenN x = 2)
      (memN (carN x) V)   -- thy
  | 16, x => (lenN x = 3)   -- mp
  | 17, x => And (lenN x = 3) ((carN x) = forallcN (nthN x (2)))   -- gen
  | 18, x => And (lenN x = 3) (And (hasWitFN (nthN x (2))) ((carN x) = implcN (substfcN 0 (TC0) (nthN x (2))) (implcN (forallcN (implcN (nthN x (2)) (substfcN 0 (TCS) (liftfcN 1 (nthN x (2)))))) (forallcN (nthN x (2))))))   -- ind
  | 19, x => And (lenN x = 4) (And (hasWitFN (nthN x (2))) ((carN x) = implcN (forallcN (implcN (liftfcN 0 (nthN x (2))) (nthN x (3)))) (implcN (nthN x (2)) (forallcN (nthN x (3))))))   -- qconf
  | 20, x => And (lenN x = 3) (And (hasWitFN (nthN x (2))) ((carN x) = implcN (substfcN 0 (TNIL) (nthN x (2))) (implcN (forallcN (forallcN (implcN (liftfcN 1 (nthN x (2))) (substfcN 0 (TCONS) (liftfcN 2 (liftfcN 1 (nthN x (2)))))))) (forallcN (nthN x (2))))))   -- listInd
  | _, _ => False

/-- `lineWF`: etiqueta ≤ 20 y la RHS de su etiqueta. Así `ax_lineWF_inv` vale por construcción. `V` es el valor
    de `axiomsCodeT` (la regla `thy` mira dentro): todo es PARAMÉTRICO en él, y sólo el ancla lo fija en `V₀`. -/
def lineWFN (V x : Nat) : Prop := And (nthN x 1 < 21) (lineWFT V (nthN x 1) x)

theorem lineWFN_of_tag {V x K : Nat} (h : nthN x 1 = K) (hK : K < 21) : lineWFN V x ↔ lineWFT V K x := by
  rw [lineWFN, h]
  exact ⟨fun h' => h'.2, fun h' => ⟨hK, h'⟩⟩

def chainOkL (V : Nat) : Nat → List Nat → Prop
  | _, [] => True
  | c, x :: r => And (And (lineWFN V x) (allInN c (premsOfN x))) (chainOkL V (concatN c (consN (carN x) 0)) r)

def chainOkN (V c p : Nat) : Prop := chainOkL V c (decodeL p)

theorem chainOkN_zero (V c : Nat) : chainOkN V c 0 := by rw [chainOkN, decodeL_zero]; trivial

theorem chainOkN_consN (V c x r : Nat) : chainOkN V c (consN x r) ↔
    And (And (lineWFN V x) (allInN c (premsOfN x))) (chainOkN V (concatN c (consN (carN x) 0)) r) := by
  rw [chainOkN, decodeL_consN]; exact Iff.rfl

end Listas

end ROBINSON_PlusPlus.Meta.ModeloCodigo

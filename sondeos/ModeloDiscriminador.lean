import ROBINSON_PlusPlus
import FOL.Semantics

/-!
# SONDEO · M1–M4, el DISCRIMINADOR del frente «modelo de los 141 axiomas»

**Fecha**: 2026‑09‑22. **Pregunta**: `goedel_second_prf` es condicional en `ConsistentH`, y
**nada lo prueba**. Un modelo en Lean de los 141 axiomas lo daría. ¿Es alcanzable?

## Resultado

| | qué se midió | resultado |
|---|---|---|
| **M1** | ¿de qué depende el ENUNCIADO `ConsistentH ↔ ¬ Prf ⊥`? | ✅ `[propext, Classical.choice, Quot.sound]` — **cero axiomas del proyecto** ⇒ un modelo lo descarga ENTERO |
| **M2** | ¿es tratable la mecánica de `evalFormula` sobre un axioma real? | ✅ `intro v d; simp […]`, y sale **`[propext]`** — el mejor footprint posible |
| **M3** | ¿se puede montar la capa de LISTAS sobre ℕ? | ✅ la inyectividad de Cantor es **net‑0 pura**; `carc` existe como inversa clásica |
| **M4** | ¿cuánto de la solidez de `Prf` está construido? | ✅ **el aparato semántico entero** (13 lemas en `FOL/Semantics.lean`), probado por `lkc_sound` |

## ⛔ Lo que M3 encontró en contra, y hay que decirlo

1. **`Nat.sqrt` NO está en el core.** `coreAxioms` tiene `ax14_sqrt_le` y `ax15_lt_succ_sqrt`,
   así que el modelo tendrá que **definir** una raíz entera y probar esas dos. Es acotado, pero
   no es gratis.
2. **Sin Mathlib no hay `ring` ni `by_contra`.** La aritmética va a mano con `Nat.succ_mul` /
   `Nat.mul_succ` + `omega`, y `omega` **no ve** un producto como `s*(s+1)/2`: hay que definir
   el número triangular **por recursión** para que lo trate linealmente.

🔑 *El obstáculo del frente no era la matemática: era qué trae el core de Lean sin Mathlib.*

## ⭐ Lo que M4 ahorra

La parte cara de toda solidez —la semántica de sustitución y lifting— **ya está**:
`eval_substFormula_ext/_zero`, `eval_liftFormula_ext/_zero`, `contextSatisfies_lift_zero`,
`shift_updateEnv_subst_comm`, y sus gemelos de término. `lkc_sound` (14 reglas) los usa, así que
están probados en uso. ⇒ la solidez de `Prf` es **inducción sobre `Prf`** reusándolos, y M‑11 no
la bloquea porque `Prf` está en la lista blanca.

## Cómo re‑ejecutarlo

    lake env lean sondeos/ModeloDiscriminador.lean      # desde la raíz de RPP
-/

/-! ⛔⛔ **LOS `open` VAN ACOTADOS, y no es estilo.** Las dos trampas se muerden:
* con `Minimal.Axioms` abierto, **`≤` resuelve al símbolo OBJETO `le`** (trampa documentada);
* y esquivarla escribiendo `Nat.le` explícito **ciega a `omega`** (ADR‑078).

M3 es aritmética de `Nat` pura y va **fuera** del `open`; M1/M2 hablan de los axiomas y van
dentro. 🔑 *Cuando dos trampas de notación se muerden, la salida no es elegir una: es acotar
el `open` para que no coincidan.* -/

namespace ModeloDiscriminador

/-! ## M3 · la capa de listas sobre ℕ (aritmética pura — SIN `open Axioms`) -/


/-- Número triangular **por recursión**: con `s*(s+1)/2` `omega` no puede (producto opaco). -/
def T : Nat → Nat
  | 0 => 0
  | s + 1 => T s + (s + 1)

theorem two_T (s : Nat) : 2 * T s = s * (s + 1) := by
  induction s with
  | zero => rfl
  | succ n ih =>
      have e1 : (n+1) * (n+1+1) = n * (n+1+1) + (n+1+1) := Nat.succ_mul n (n+1+1)
      have e2 : n * (n+1+1) = n * (n+1) + n := Nat.mul_succ n (n+1)
      simp only [T]
      omega

/-- ⚠️ `Nat.le` EXPLÍCITO: con `Minimal.Axioms` abierto, `≤` resuelve al símbolo OBJETO `le`.
    La trampa está documentada y aun así saltó al promover el sondeo — en el scratchpad no
    estaba ese `open`. 🔑 *Un sondeo compila en SU contexto de `open`s.* -/
theorem T_le_of_le : ∀ {a b : Nat}, a ≤ b → T a ≤ T b
  | a, 0, h => by have : a = 0 := by omega
                  subst this; exact Nat.le_refl _
  | a, b + 1, h => by
      rcases Nat.lt_or_ge a (b + 1) with h' | h'
      · have := T_le_of_le (a := a) (b := b) (by omega)
        simp only [T]; omega
      · have : a = b + 1 := by omega
        subst this; exact Nat.le_refl _

/-- `cantor_func x y = div2 ((x+y)(x+y+1) + 2y)` es exactamente esto. -/
def pairN (x y : Nat) : Nat := T (x + y) + y

theorem pairN_eq_div2 (x y : Nat) :
    pairN x y = ((x + y) * (x + y + 1) + 2 * y) / 2 := by
  have h := two_T (x + y)
  simp only [pairN]; omega

/-- ⭐⭐ **EL CRUX de M3**: el emparejamiento de Cantor es INYECTIVO. Net‑0 puro. -/
theorem pairN_inj {x y x' y' : Nat} (h : pairN x y = pairN x' y') :
    And (x = x') (y = y') := by
  have hs : x + y = x' + y' := by
    rcases Nat.lt_or_ge (x + y) (x' + y') with hlt | hge
    · exfalso
      have h1 := T_le_of_le (a := x + y + 1) (b := x' + y') (by omega)
      simp only [T] at h1; simp only [pairN] at h; omega
    · rcases Nat.lt_or_ge (x' + y') (x + y) with hlt' | hge'
      · exfalso
        have h1 := T_le_of_le (a := x' + y' + 1) (b := x + y) (by omega)
        simp only [T] at h1; simp only [pairN] at h; omega
      · omega
  simp only [pairN, hs] at h
  exact ⟨by omega, by omega⟩

/-! ## M1 y M2 · aquí SÍ hacen falta los axiomas — `open` acotado a esta sección -/

section Axiomas
open FOL
open FOL.Metamath.Semantics
open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.Godel

theorem m1_stmt : ConsistentH ↔ ¬ Prf Formula.bottom := Iff.rfl

/-! ## M2 · la mecánica: un modelo mínimo sobre ℕ y un axioma core VALIDADO -/

def MN : Model Nat where
  func := fun s args =>
    match s, args with
    | "0", []      => 0
    | "S", [a]     => a + 1
    | "+", [a, b]  => a + b
    | "*", [a, b]  => a * b
    | _, _         => 0
  rel := fun _ _ => False

theorem m2_add_zero : ∀ (v : Nat → Nat), evalFormula MN v ax4_add_zero := by
  intro v d
  simp [add, zero, add_sym, zero_sym, evalFormula, evalTerm, evalTerms, shiftEnv, MN]

end Axiomas

end ModeloDiscriminador

open Classical

/-- ⇒ `carc` EXISTE: la inversa, **clásicamente**. La interpretación de un modelo no tiene que
    ser computable — `ModelG.func` es una función de Lean cualquiera. -/
noncomputable def carcN (c : Nat) : Nat :=
  if h : ∃ x y, ModeloDiscriminador.pairN x (y + 1) = c then h.choose else 0

theorem carcN_cons (h t : Nat) : carcN (ModeloDiscriminador.pairN h (t + 1)) = h := by
  have hex : ∃ x y, ModeloDiscriminador.pairN x (y + 1)
      = ModeloDiscriminador.pairN h (t + 1) := ⟨h, t, rfl⟩
  simp only [carcN, dif_pos hex]
  obtain ⟨y', hy'⟩ := hex.choose_spec
  exact (ModeloDiscriminador.pairN_inj hy').1

#print axioms ModeloDiscriminador.m1_stmt
#print axioms ModeloDiscriminador.m2_add_zero
#print axioms ModeloDiscriminador.pairN_inj
#print axioms carcN_cons

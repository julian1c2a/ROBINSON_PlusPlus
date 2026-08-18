/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.CodeTreeReflect

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.CheckArith
open ROBINSON_PlusPlus.Meta.Sigma1Prf
open ROBINSON_PlusPlus.Meta.LineWFTrackedPrf
open ROBINSON_PlusPlus.Meta.LineWFSchemaPrf
open ROBINSON_PlusPlus.Meta.CodeTreeReflect

namespace ROBINSON_PlusPlus.Meta.LineWFPropPrf

/-!
## META — NIVEL D real (B.3c): los tags de ÁRBOL PURO (9 proposicionales + `gen`)

Con `CodeTreeReflect` cada tag estructural se reduce a **declarar su árbol** y comprobar que el
esquema estricto coincide definicionalmente con la forma que el chasis espera. El coste por tag
baja de ~100 líneas (piloto `efq`) a **tres declaraciones**.

Diccionario de tags de constructor: `botc` = `nul 2`, `implc` = `bin 5`, `andc` = `bin 7`,
`orc` = `bin 8`; `leaf i` = `nthc · i`.
-/

/-- P1 (tag 0, longitud 4): `a ⇒ (b ⇒ a)`. -/
def tP1 : CTree := .bin 5 (.leaf 2) (.bin 5 (.leaf 3) (.leaf 2))
theorem ax_p1_eq : ax_lineWF_p1
    = Formula.forall (Formula.impl (tagF 0) (lwfVar ⇔ Formula.and (lencF 4) (condOf tP1))) := rfl
theorem pcc_lineWF_tracked_p1_imp (t : Term) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM 0) ⇒
      provFromCode (lineWFCodeFn (tcFn t)))) :=
  pcc_lineWF_tracked_of_tree tP1 t
    (ax_p1_eq ▸ prf_ax (show ax_lineWF_p1 ∈ axioms by simp [axioms])) (Nat.le_refl _) (by decide)

/-- P2 (tag 1, longitud 5): `(a ⇒ (b ⇒ c)) ⇒ ((a ⇒ b) ⇒ (a ⇒ c))`. -/
def tP2 : CTree :=
  .bin 5 (.bin 5 (.leaf 2) (.bin 5 (.leaf 3) (.leaf 4)))
         (.bin 5 (.bin 5 (.leaf 2) (.leaf 3)) (.bin 5 (.leaf 2) (.leaf 4)))
theorem ax_p2_eq : ax_lineWF_p2
    = Formula.forall (Formula.impl (tagF 1) (lwfVar ⇔ Formula.and (lencF 5) (condOf tP2))) := rfl
theorem pcc_lineWF_tracked_p2_imp (t : Term) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM 1) ⇒
      provFromCode (lineWFCodeFn (tcFn t)))) :=
  pcc_lineWF_tracked_of_tree tP2 t
    (ax_p2_eq ▸ prf_ax (show ax_lineWF_p2 ∈ axioms by simp [axioms])) (Nat.le_refl _) (by decide)

/-- C1 (tag 2, longitud 4): `a ⇒ (b ⇒ (a ∧ b))`. -/
def tC1 : CTree := .bin 5 (.leaf 2) (.bin 5 (.leaf 3) (.bin 7 (.leaf 2) (.leaf 3)))
theorem ax_c1_eq : ax_lineWF_c1
    = Formula.forall (Formula.impl (tagF 2) (lwfVar ⇔ Formula.and (lencF 4) (condOf tC1))) := rfl
theorem pcc_lineWF_tracked_c1_imp (t : Term) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM 2) ⇒
      provFromCode (lineWFCodeFn (tcFn t)))) :=
  pcc_lineWF_tracked_of_tree tC1 t
    (ax_c1_eq ▸ prf_ax (show ax_lineWF_c1 ∈ axioms by simp [axioms])) (Nat.le_refl _) (by decide)

/-- C2 (tag 3, longitud 4): `(a ∧ b) ⇒ a`. -/
def tC2 : CTree := .bin 5 (.bin 7 (.leaf 2) (.leaf 3)) (.leaf 2)
theorem ax_c2_eq : ax_lineWF_c2
    = Formula.forall (Formula.impl (tagF 3) (lwfVar ⇔ Formula.and (lencF 4) (condOf tC2))) := rfl
theorem pcc_lineWF_tracked_c2_imp (t : Term) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM 3) ⇒
      provFromCode (lineWFCodeFn (tcFn t)))) :=
  pcc_lineWF_tracked_of_tree tC2 t
    (ax_c2_eq ▸ prf_ax (show ax_lineWF_c2 ∈ axioms by simp [axioms])) (Nat.le_refl _) (by decide)

/-- C3 (tag 4, longitud 4): `(a ∧ b) ⇒ b`. -/
def tC3 : CTree := .bin 5 (.bin 7 (.leaf 2) (.leaf 3)) (.leaf 3)
theorem ax_c3_eq : ax_lineWF_c3
    = Formula.forall (Formula.impl (tagF 4) (lwfVar ⇔ Formula.and (lencF 4) (condOf tC3))) := rfl
theorem pcc_lineWF_tracked_c3_imp (t : Term) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM 4) ⇒
      provFromCode (lineWFCodeFn (tcFn t)))) :=
  pcc_lineWF_tracked_of_tree tC3 t
    (ax_c3_eq ▸ prf_ax (show ax_lineWF_c3 ∈ axioms by simp [axioms])) (Nat.le_refl _) (by decide)

/-- J1 (tag 5, longitud 4): `a ⇒ (a ∨ b)`. -/
def tJ1 : CTree := .bin 5 (.leaf 2) (.bin 8 (.leaf 2) (.leaf 3))
theorem ax_j1_eq : ax_lineWF_j1
    = Formula.forall (Formula.impl (tagF 5) (lwfVar ⇔ Formula.and (lencF 4) (condOf tJ1))) := rfl
theorem pcc_lineWF_tracked_j1_imp (t : Term) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM 5) ⇒
      provFromCode (lineWFCodeFn (tcFn t)))) :=
  pcc_lineWF_tracked_of_tree tJ1 t
    (ax_j1_eq ▸ prf_ax (show ax_lineWF_j1 ∈ axioms by simp [axioms])) (Nat.le_refl _) (by decide)

/-- J2 (tag 6, longitud 4): `b ⇒ (a ∨ b)`. -/
def tJ2 : CTree := .bin 5 (.leaf 3) (.bin 8 (.leaf 2) (.leaf 3))
theorem ax_j2_eq : ax_lineWF_j2
    = Formula.forall (Formula.impl (tagF 6) (lwfVar ⇔ Formula.and (lencF 4) (condOf tJ2))) := rfl
theorem pcc_lineWF_tracked_j2_imp (t : Term) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM 6) ⇒
      provFromCode (lineWFCodeFn (tcFn t)))) :=
  pcc_lineWF_tracked_of_tree tJ2 t
    (ax_j2_eq ▸ prf_ax (show ax_lineWF_j2 ∈ axioms by simp [axioms])) (Nat.le_refl _) (by decide)

/-- J3 (tag 7, longitud 5): `(a ∨ b) ⇒ ((a ⇒ c) ⇒ ((b ⇒ c) ⇒ c))`. -/
def tJ3 : CTree :=
  .bin 5 (.bin 8 (.leaf 2) (.leaf 3))
         (.bin 5 (.bin 5 (.leaf 2) (.leaf 4))
                 (.bin 5 (.bin 5 (.leaf 3) (.leaf 4)) (.leaf 4)))
theorem ax_j3_eq : ax_lineWF_j3
    = Formula.forall (Formula.impl (tagF 7) (lwfVar ⇔ Formula.and (lencF 5) (condOf tJ3))) := rfl
theorem pcc_lineWF_tracked_j3_imp (t : Term) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM 7) ⇒
      provFromCode (lineWFCodeFn (tcFn t)))) :=
  pcc_lineWF_tracked_of_tree tJ3 t
    (ax_j3_eq ▸ prf_ax (show ax_lineWF_j3 ∈ axioms by simp [axioms])) (Nat.le_refl _) (by decide)

/-- P3 (tag 14, longitud 3): `((a ⇒ ⊥) ⇒ ⊥) ⇒ a`. -/
def tP3 : CTree := .bin 5 (.bin 5 (.bin 5 (.leaf 2) (.nul 2)) (.nul 2)) (.leaf 2)
theorem ax_p3_eq : ax_lineWF_p3
    = Formula.forall (Formula.impl (tagF 14) (lwfVar ⇔ Formula.and (lencF 3) (condOf tP3))) := rfl
theorem pcc_lineWF_tracked_p3_imp (t : Term) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM 14) ⇒
      provFromCode (lineWFCodeFn (tcFn t)))) :=
  pcc_lineWF_tracked_of_tree tP3 t
    (ax_p3_eq ▸ prf_ax (show ax_lineWF_p3 ∈ axioms by simp [axioms])) (Nat.le_refl _) (by decide)

/-- GEN (tag 17, longitud 3): `∀ body`. Único de los cuantificacionales que es árbol **puro**
    (los demás llevan `substfc`/`liftfc`, que no son constructores de código sino funciones objeto). -/
def tGen : CTree := .un 6 (.leaf 2)
theorem ax_gen_eq : ax_lineWF_gen
    = Formula.forall (Formula.impl (tagF 17) (lwfVar ⇔ Formula.and (lencF 3) (condOf tGen))) := rfl
theorem pcc_lineWF_tracked_gen_imp (t : Term) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM 17) ⇒
      provFromCode (lineWFCodeFn (tcFn t)))) :=
  pcc_lineWF_tracked_of_tree tGen t
    (ax_gen_eq ▸ prf_ax (show ax_lineWF_gen ∈ axioms by simp [axioms])) (Nat.le_refl _) (by decide)

end ROBINSON_PlusPlus.Meta.LineWFPropPrf

export ROBINSON_PlusPlus.Meta.LineWFPropPrf (
  tP1 tP2 tC1 tC2 tC3 tJ1 tJ2 tJ3 tP3 tGen
  ax_p1_eq ax_p2_eq ax_c1_eq ax_c2_eq ax_c3_eq ax_j1_eq ax_j2_eq ax_j3_eq ax_p3_eq ax_gen_eq
  pcc_lineWF_tracked_p1_imp pcc_lineWF_tracked_p2_imp
  pcc_lineWF_tracked_c1_imp pcc_lineWF_tracked_c2_imp pcc_lineWF_tracked_c3_imp
  pcc_lineWF_tracked_j1_imp pcc_lineWF_tracked_j2_imp pcc_lineWF_tracked_j3_imp
  pcc_lineWF_tracked_p3_imp pcc_lineWF_tracked_gen_imp
)

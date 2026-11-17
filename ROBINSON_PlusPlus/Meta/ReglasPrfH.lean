/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.ReprPrf
import ROBINSON_PlusPlus.Meta.HilbertDeduction

/-!
# `Meta/ReglasPrfH.lean` — diez reglas derivadas de `PrfH`, por debajo de la aritmética (ADR‑270)

**Qué.** En `PrfH`, el cálculo con contexto del teorema de deducción: Leibniz (`PrfH_leibniz_subst`) y lo que sale de
ella —la transitividad y la simetría de `=eq`, la congruencia de `<` en sus dos argumentos y la de `cons` en la
cabeza—; el `⇔` con un bicondicional cerrado (`PrfH_iff_mp`, `PrfH_iff_mpr`); y la eliminación de `∨` (`PrfH_or_elim`)
y la del `∀` (`PrfH_spec`).

**Por qué aquí** (A9 y el paso 3 de B1, ADR‑270). Vivían en `Meta/ChainPrf.lean`, y eran lo ÚNICO que la cadena
aritmética (`NatArithPrf` … `Div2ParityPrf`) y `Meta/ListIndAdmisible.lean` tomaban de él (medido con el elaborador:
`doc/registro/2026-11-18-capas-paso3/`). Con ellas abajo, la aritmética no importa `ChainPrf`, y `ChainPrf` puede
importar `ListIndAdmisible` y demostrar `prf_list_induction` sin el constructor `Prf.listInd`. Mismos enunciados y
pruebas; cambia el espacio de nombres (el del módulo, NAMING‑CONVENTIONS §6). Salen a la raíz las diez (AI‑GUIDE §17:
las usan otros módulos); antes salían cuatro, y las otras seis se usaban con `open …ChainPrf`.
-/

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.HilbertDeduction

namespace ROBINSON_PlusPlus.Meta.ReglasPrfH

/-- Leibniz en `PrfH`: de `PrfH Γ (t₁ ≐ t₂)` y `PrfH Γ A[t₁]` sale `PrfH Γ A[t₂]`. -/
theorem PrfH_leibniz_subst {Γ : List Formula} {A : Formula} {t₁ t₂ : Term}
    (h : PrfH Γ (t₁ =eq t₂)) (hA : PrfH Γ (substFormula 0 t₁ A)) : PrfH Γ (substFormula 0 t₂ A) :=
  PrfH.mp Γ _ _ (PrfH.mp Γ _ _ (PrfH.incl0 Γ _ (Prfᵢ.leibniz A t₁ t₂)) h) hA

/-- Transitividad de `=eq` en `PrfH`. -/
theorem PrfH_eq_trans {Γ : List Formula} {a b c : Term}
    (h1 : PrfH Γ (a =eq b)) (h2 : PrfH Γ (b =eq c)) : PrfH Γ (a =eq c) := by
  let f : Formula := Formula.eq (liftTerm 0 a) (.var 0)
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq a s := by
    intro s; simp only [f, substFormula, substTerm, FOL.substTerm_liftTerm, ite_true]
  exact (hS c) ▸ PrfH_leibniz_subst (A := f) h2 ((hS b) ▸ h1)

/-- Simetría de `=eq` en `PrfH`. -/
theorem PrfH_eq_symm {Γ : List Formula} {a b : Term} (h : PrfH Γ (a =eq b)) : PrfH Γ (b =eq a) := by
  let f : Formula := Formula.eq (.var 0) (liftTerm 0 a)
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq s a := by
    intro s; simp only [f, substFormula, substTerm, FOL.substTerm_liftTerm, ite_true]
  exact (hS b) ▸ PrfH_leibniz_subst (A := f) h ((hS a) ▸ prf_to_prfH (prf_refl a) Γ)

/-- ⭐ Congruencia de `<` en el 1er argumento, en `PrfH`.

    ⚠️ **Bajó aquí en el dedup del 2026‑09‑09d** (ADR‑019). Estaba declarada dos veces, en
    `Meta/BoundedInPrf.lean` y en `Meta/NatOrderPrf.lean`, **las dos exportadas a la raíz**. Y
    el duplicado era CONSCIENTE: el docstring de `NatOrderPrf` decía «copia local: el original
    vive en `BoundedInPrf`, que es posterior a este módulo en la cadena de imports». Esa es
    exactamente la situación que ADR‑019 resuelve **bajando el general**, no copiándolo.
    (✏️ 2026‑11‑18, ADR‑270: aquel «aquí» era `Meta/ChainPrf.lean`; ésta y las otras nueve bajaron otra vez, a este
    módulo, por la misma razón.) -/
theorem PrfH_lt_subst1 {Γ : List Formula} {a₁ a₂ b : Term} (h : PrfH Γ (a₁ =eq a₂))
    (hlt : PrfH Γ (lt a₁ b)) : PrfH Γ (lt a₂ b) := by
  let f : Formula := lt (.var 0) (liftTerm 0 b)
  have hS : ∀ s : Term, substFormula 0 s f = lt s b := by
    intro s; simp only [f, lt, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, ite_true]
  exact (hS a₂) ▸ PrfH_leibniz_subst (A := f) h ((hS a₁) ▸ hlt)

/-- ⭐ Congruencia de `<` en el 2º argumento, en `PrfH`. Misma historia que la anterior; ésta es
    la que tenía **53 referencias cualificadas** `PrfH_lt_subst2` por el árbol. -/
theorem PrfH_lt_subst2 {Γ : List Formula} {a b₁ b₂ : Term} (h : PrfH Γ (b₁ =eq b₂))
    (hlt : PrfH Γ (lt a b₁)) : PrfH Γ (lt a b₂) := by
  let f : Formula := lt (liftTerm 0 a) (.var 0)
  have hS : ∀ s : Term, substFormula 0 s f = lt a s := by
    intro s; simp only [f, lt, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, ite_true]
  exact (hS b₂) ▸ PrfH_leibniz_subst (A := f) h ((hS b₁) ▸ hlt)

/-- Congruencia de `cons` en la cabeza, en `PrfH`. -/
theorem PrfH_congr_cons_head {Γ : List Formula} {hd₁ hd₂ t : Term}
    (h : PrfH Γ (hd₁ =eq hd₂)) : PrfH Γ (cons hd₁ t =eq cons hd₂ t) := by
  let f : Formula := Formula.eq (cons (liftTerm 0 hd₁) (liftTerm 0 t)) (cons (.var 0) (liftTerm 0 t))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (cons hd₁ t) (cons s t) := by
    intro s; simp only [f, substFormula, cons, substTerm, substTerms, FOL.substTerm_liftTerm, ite_true]
  exact (hS hd₂) ▸ PrfH_leibniz_subst (A := f) h ((hS hd₁) ▸ prf_to_prfH (prf_refl (cons hd₁ t)) Γ)

/-- `iff`-mp con un bicondicional **cerrado** (`Prf`) y una hipótesis `PrfH`. -/
theorem PrfH_iff_mp {Γ : List Formula} {A B : Formula} (hiff : Prf (A ⇔ B)) (ha : PrfH Γ A) :
    PrfH Γ B :=
  PrfH.mp Γ _ _ (prf_to_prfH (prf_and_elim_left hiff) Γ) ha

theorem PrfH_iff_mpr {Γ : List Formula} {A B : Formula} (hiff : Prf (A ⇔ B)) (hb : PrfH Γ B) :
    PrfH Γ A :=
  PrfH.mp Γ _ _ (prf_to_prfH (prf_and_elim_right hiff) Γ) hb

/-- Eliminación de la disyunción en `PrfH` (vía `Prfᵢ.j3` + teorema de deducción). -/
theorem PrfH_or_elim {Γ : List Formula} {A B C : Formula} (hor : PrfH Γ (lor A B))
    (hA : PrfH (A :: Γ) C) (hB : PrfH (B :: Γ) C) : PrfH Γ C :=
  PrfH.mp Γ _ _ (PrfH.mp Γ _ _ (PrfH.mp Γ _ _ (PrfH.incl0 Γ _ (Prfᵢ.j3 A B C)) hor)
    (deduction_aux hA A Γ rfl)) (deduction_aux hB B Γ rfl)

/-- `∀-elim` en `PrfH` (vía `Prfᵢ.q1` + `mp`). Helper para la HI-`∀c` del `step`. -/
theorem PrfH_spec {Γ : List Formula} {A : Formula} (h : PrfH Γ (Formula.forall A)) (t : Term) :
    PrfH Γ (substFormula 0 t A) :=
  PrfH.mp Γ _ _ (PrfH.incl0 Γ _ (Prfᵢ.q1 A t)) h

end ROBINSON_PlusPlus.Meta.ReglasPrfH

export ROBINSON_PlusPlus.Meta.ReglasPrfH (
  PrfH_congr_cons_head PrfH_eq_symm PrfH_eq_trans PrfH_iff_mp PrfH_iff_mpr PrfH_leibniz_subst
  PrfH_lt_subst1 PrfH_lt_subst2 PrfH_or_elim PrfH_spec
)

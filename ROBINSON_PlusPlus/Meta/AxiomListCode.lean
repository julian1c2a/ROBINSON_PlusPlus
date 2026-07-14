/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.ReprPrf
import ROBINSON_PlusPlus.Meta.CodeDistinct

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.CodeDistinct
open ROBINSON_PlusPlus.Meta.Representability
open ROBINSON_PlusPlus.Meta.ReprPrf

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Meta.AxiomListCode

/-!
## META — NIVEL D real (§42): pertenencia (± ) al código de una lista de fórmulas

Infraestructura para **concretar `axiomsCodeT`** (opción 1 del `PLAN-NEGVERIFIER.md`): la teoría
decide la pertenencia de un código de fórmula a `listFormCodeM L` **sin materializar el término
gigante**. La clave es la **recursión estructural sobre `L` ABSTRACTA** (cada paso usa `ax_L1`/`ax_L2`
+ la (des)igualdad de la cabeza), de modo que `listFormCodeM axioms` **nunca se expande** — evita el
coste de ~40 s que motivó retirar el `axiomsCodeT` concreto en `7ae7b7b`.

* **Positivo** `prf_In_listFormCodeM`: `f ∈ L ⟹ ⊢ In ⌜f⌝ (listFormCodeM L)` (reflexividad + recursión).
* **Negativo** `prf_not_In_listFormCodeM`: `f ∉ L ⟹ ⊢ ¬ In ⌜f⌝ (listFormCodeM L)` (`formCode_ne` + rec.).
* **Corolario** `neg_In_axiomsList_of_not_prf`: `¬ Prf φ ⟹ ⊢ ¬ In ⌜φ⌝ (listFormCodeM axioms)` — vía
  `prf_ax` (los axiomas son demostrables), **sin comparación sintáctica** de la lista.
-/

/-- `¬ In x nil` a nivel `axioms ⊢` (instancia de `ax_L1_in_nil`). -/
theorem prf_not_in_nil_D (x : Term) : axioms ⊢ neg (In x nil) := by
  have hh := spec (ax (show ax_L1_in_nil ∈ axioms by simp [axioms])) x
  simpa [ax_L1_in_nil, neg, substFormula, substTerm, substTerms, In, nil, zero,
    FOL.substTerm_liftTerm] using hh

/-- **Pertenencia NEGATIVA** al código de una lista: si `f ∉ L`, la teoría **refuta** `In ⌜f⌝ …`.
    (El positivo `prf_In_listFormCodeM` y `prf_in_cons_iff_D` viven en `Minimal/Axioms`, junto al
    anclaje `ax_axiomsCodeT_eq`; aquí sólo el negativo, que necesita `formCode_ne`, nivel Meta.) -/
theorem prf_not_In_listFormCodeM (φ : Formula) :
    ∀ (L : List Formula), ¬ List.Mem φ L → axioms ⊢ neg (In (formCode φ) (listFormCodeM L))
  | [], _ => by simpa [listFormCodeM] using prf_not_in_nil_D (formCode φ)
  | f :: fs, hmem => by
      have hne_head : axioms ⊢ neg (formCode φ =eq formCodeM f) := by
        have hφ : φ ≠ f := fun e => hmem (e ▸ List.mem_cons.mpr (Or.inl rfl))
        rw [formCodeM_eq]; exact formCode_ne hφ
      have hne_tail : axioms ⊢ neg (In (formCode φ) (listFormCodeM fs)) :=
        prf_not_In_listFormCodeM φ fs (fun m => hmem (List.mem_cons.mpr (Or.inr m)))
      show axioms ⊢ neg (In (formCode φ) (cons (formCodeM f) (listFormCodeM fs)))
      apply raa; intro h_in
      have h_disj := iff_mp (prf_in_cons_iff_D (formCode φ) (formCodeM f) (listFormCodeM fs)) h_in
      apply FOL.MetaRules.or_elim h_disj
      · intro h_eq; exact mp hne_head h_eq
      · intro h_in_tail; exact mp hne_tail h_in_tail

/-- **Corolario — la refutación que necesita `NegVerifier`**: `¬ Prf φ ⟹ ⊢ ¬ In ⌜φ⌝ (listFormCodeM
    axioms)`. Se obtiene `φ ∉ axioms` de `¬ Prf φ` vía `prf_ax` (todo axioma es demostrable), **sin
    recorrer sintácticamente** la lista de axiomas. -/
theorem neg_In_axiomsList_of_not_prf (φ : Formula) (hnp : ¬ Prf φ) :
    axioms ⊢ neg (In (formCode φ) (listFormCodeM axioms)) :=
  prf_not_In_listFormCodeM φ axioms (fun hmem => hnp (prf_ax hmem))

/-- **DIRECCIÓN NEGATIVA DE `axiomsCodeT`** — la pieza que desbloquea `NegVerifier`: si `φ` no es
    demostrable, la teoría **refuta** que `⌜φ⌝` sea un axioma (`In ⌜φ⌝ axiomsCodeT`). Transporta
    `neg_In_axiomsList_of_not_prf` a `axiomsCodeT` por el anclaje `ax_axiomsCodeT_eq` (`Derives.subst`
    sobre el segundo argumento de `In`). Es el **espejo negativo** de `ax_inAxC`. -/
theorem neg_In_axiomsCodeT (φ : Formula) (hnp : ¬ Prf φ) :
    axioms ⊢ neg (In (formCode φ) axiomsCodeT) := by
  have key : ∀ t : Term,
      substFormula 0 t (neg (In (formCode φ) (.var 0))) = neg (In (formCode φ) t) := by
    intro t
    rw [← formCodeM_eq φ]
    simp [neg, In, substFormula, substTerm, substTerms, substTerm_formCodeM, FOL.substTerm_liftTerm]
  have hpos : axioms ⊢ substFormula 0 (listFormCodeM axioms) (neg (In (formCode φ) (.var 0))) := by
    rw [key]; exact neg_In_axiomsList_of_not_prf φ hnp
  have hsub := Derives.subst axioms (listFormCodeM axioms) axiomsCodeT
    (neg (In (formCode φ) (.var 0))) (FOL.derive_eq_symm ax_axiomsCodeT_eq) hpos
  rwa [key] at hsub

end ROBINSON_PlusPlus.Meta.AxiomListCode

export ROBINSON_PlusPlus.Meta.AxiomListCode (
  prf_not_in_nil_D prf_not_In_listFormCodeM
  neg_In_axiomsList_of_not_prf neg_In_axiomsCodeT
)

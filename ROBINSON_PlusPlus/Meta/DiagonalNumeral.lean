/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.CodeNumeralPrf
import ROBINSON_PlusPlus.Meta.DiagonalTwo

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.SubstArith
open ROBINSON_PlusPlus.Meta.Induction
open ROBINSON_PlusPlus.Meta.Diagonal
open ROBINSON_PlusPlus.Meta.DiagonalTwo
open ROBINSON_PlusPlus.Meta.ProofChain
open ROBINSON_PlusPlus.Meta.CodeNumeralPrf
open FOL
open FOL.MetaRules

set_option maxHeartbeats 1000000

namespace ROBINSON_PlusPlus.Meta.DiagonalNumeral

/-!
## META — **el lema diagonal con códigos NUMERALES** (la reparación de la inconsistencia)

`Meta/Diagonal.lean` construye el punto fijo con `tc_form`, o sea con la lectura **sintáctica** de
`tcFn`, que es la que hace inconsistente la teoría (`ax_tc_cons`). Este módulo lo reconstruye con
la lectura **NUMERAL**, que es consistente y tiene modelo en ℕ.

**La pieza que lo hace posible** es `prf_formCode_numeral` (`Meta/CodeNumeralPrf.lean`):
`formCode φ =eq numeral (codeNat φ)`. Con ella, `tcFn` sólo necesita `ax_tc_zero`/`ax_tc_succ`.

**Por qué la sustitución funciona sin refundar nada:** `substFormula_arith (v) (s) (f)` acepta un
`s` **ARBITRARIO**, luego traga un numeral igual que tragaba un árbol; y `godelPred'`, `godelBeta'`,
`diagTerm` y `godel_comp'` **no mencionan la representación del código**, así que se reutilizan tal
cual. El resultado se compone con `provCode_transfer` para dejarlo en la forma exacta que el
argumento modular de Gödel (`goedel_first_unprovable_real'`) espera.
-/

/-! ### La equivalencia entre representaciones -/

/-- El numeral del código y el árbol de código denotan lo mismo. Es `prf_formCode_numeral`
    trasladado a la capa ω. -/
theorem hFN (φ : Formula) : axioms ⊢ (numeral (codeNat φ) =eq formCode φ) :=
  FOL.derive_eq_symm (prf_to_derives (prf_formCode_numeral φ))

/-! ### La sentencia de Gödel, con el código escrito como NUMERAL -/

/-- `selfApp` con el código en forma numeral. -/
noncomputable def selfAppN (ψ : Formula) : Formula := substFormula 0 (numeral (codeNat ψ)) ψ

/-- `Prov'(⌜φ⌝)` con el código en forma numeral. -/
noncomputable def provCodeN (φ : Formula) : Formula :=
  substFormula 0 (numeral (codeNat φ)) provFormulaC'

/-- **Sentencia de Gödel numeral.** `godelBeta'` se reutiliza sin cambios. -/
noncomputable def godelCN : Formula := selfAppN godelBeta'

/-! ### `diag_arith` por la vía numeral -/

/-- **Representabilidad de la diagonalización, sin `tc_cons`.**
    `tc_numeral` sólo usa `ax_tc_zero`/`ax_tc_succ`. -/
theorem diag_arith_num (ψ : Formula) :
    axioms ⊢ (substTerm 0 (numeral (codeNat ψ)) diagTerm =eq numeral (codeNat (selfAppN ψ))) := by
  have p1 : axioms ⊢ (substfc (numeral 0) (tcFn (numeral (codeNat ψ))) (numeral (codeNat ψ)) =eq
                      substfc (numeral 0) (termCode (numeral (codeNat ψ))) (numeral (codeNat ψ))) :=
    congr_substfc_arg2 (tc_numeral (codeNat ψ))
  have p2 : axioms ⊢ (substfc (numeral 0) (termCode (numeral (codeNat ψ))) (numeral (codeNat ψ)) =eq
                      substfc (numeral 0) (termCode (numeral (codeNat ψ))) (formCode ψ)) :=
    congr_substfc_arg3 (hFN ψ)
  have p3 : axioms ⊢ (substfc (numeral 0) (termCode (numeral (codeNat ψ))) (formCode ψ) =eq
                      formCode (substFormula 0 (numeral (codeNat ψ)) ψ)) :=
    substFormula_arith 0 (numeral (codeNat ψ)) ψ
  have p4 : axioms ⊢ (formCode (selfAppN ψ) =eq numeral (codeNat (selfAppN ψ))) :=
    FOL.derive_eq_symm (hFN (selfAppN ψ))
  exact FOL.derive_eq_trans p1 (FOL.derive_eq_trans p2 (FOL.derive_eq_trans p3 p4))

/-! ### El punto fijo -/

/-- Punto fijo en la representación numeral. -/
theorem godelCN_fixedpoint_N : axioms ⊢ (godelCN ⇔ neg (provCodeN godelCN)) := by
  have hiff := subst_eq_iff godelPred' (diag_arith_num godelBeta')
  rw [← godel_comp' (numeral (codeNat godelBeta'))] at hiff
  simpa only [godelCN, selfAppN, godelPred', provCodeN, neg, substFormula] using hiff

/-- **Transferencia**: las dos representaciones de `Prov'` son equivalentes, por UN paso de
    Leibniz. Es lo que permite reutilizar D1 y el argumento de Gödel sin re‑demostrarlos. -/
theorem provCode_transfer (φ : Formula) : axioms ⊢ (provCodeN φ ⇔ provCodeC' φ) :=
  subst_eq_iff provFormulaC' (hFN φ)

/-- Congruencia de la negación bajo un bicondicional. -/
theorem neg_congr_iff {B C : Formula} (h : axioms ⊢ (B ⇔ C)) : axioms ⊢ (neg B ⇔ neg C) :=
  FOL.MetaRules.and_intro
    (imp_intro (fun hnb => imp_intro (fun hc =>
      mp hnb (mp (FOL.MetaRules.and_elim_right h) hc))))
    (imp_intro (fun hnc => imp_intro (fun hb =>
      mp hnc (mp (Minimal.Axioms.and_elim_left h) hb))))

/-- Transitividad de `⇔`. -/
theorem iff_trans {A B C : Formula} (h₁ : axioms ⊢ (A ⇔ B)) (h₂ : axioms ⊢ (B ⇔ C)) :
    axioms ⊢ (A ⇔ C) :=
  FOL.MetaRules.and_intro
    (imp_intro (fun ha => mp (Minimal.Axioms.and_elim_left h₂)
      (mp (Minimal.Axioms.and_elim_left h₁) ha)))
    (imp_intro (fun hc => mp (FOL.MetaRules.and_elim_right h₁)
      (mp (FOL.MetaRules.and_elim_right h₂) hc)))

/-- **EL PUNTO FIJO, en la forma que el argumento modular de Gödel espera** — y **sin `tc_cons`**. -/
theorem godelCN_fixedpoint : axioms ⊢ (godelCN ⇔ neg (provCodeC' godelCN)) :=
  iff_trans godelCN_fixedpoint_N (neg_congr_iff (provCode_transfer godelCN))

/-! ### Gödel I, reparado -/

/-- **PRIMER TEOREMA DE GÖDEL (indemostrabilidad), sobre la sentencia NUMERAL.**
    Mismo argumento modular que `goedel_first_real'`, con el punto fijo reparado. -/
theorem goedel_first_numeral (hcon : ConsistentOmega) : ¬ Prf godelCN :=
  goedel_first_unprovable_real' hcon godelCN_fixedpoint

/-- **Gödel I — `Gₙ` INDECIDIBLE**, con la reflexión como hipótesis explícita.
    Análogo numeral de `goedel_first_undecidable_real'`, que se retiró con el punto fijo roto. -/
theorem goedel_first_undecidable_numeral
    (hcon : ConsistentOmega) (hrefl : Reflects godelCN) :
    (¬ Prf godelCN) ∧ (¬ Prf (neg godelCN)) :=
  ⟨goedel_first_numeral hcon,
   goedel_first_unrefutable_real' hcon godelCN_fixedpoint hrefl⟩

end ROBINSON_PlusPlus.Meta.DiagonalNumeral

export ROBINSON_PlusPlus.Meta.DiagonalNumeral (
  hFN selfAppN provCodeN godelCN
  diag_arith_num godelCN_fixedpoint_N provCode_transfer
  neg_congr_iff iff_trans godelCN_fixedpoint goedel_first_numeral
  goedel_first_undecidable_numeral
)

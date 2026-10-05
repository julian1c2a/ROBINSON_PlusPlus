/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.ModeloEstandar

/-!
# `Meta/ModeloCodificacion.lean` — los 107 de codificación, el ANCLA y los 142 (ADR‑119/120)

Cada uno de los 107 de `codingAxioms` con el mismo molde: `intro` de los binders, `abre`, y el lema de
`Meta/ModeloCodigo.lean` que dice lo que el axioma dice. `validProofFn` toma su conclusión de `stepT`, sea cual sea
la condición (`mp`, `gen`, `thy`); `lineWF` es, por construcción, `etiqueta < 21 ∧ lineWFT V etiqueta`, y de ahí
salen también `ax_lineWF_inv` y `ax_lineWF_cons`.

**El ancla** (`v_ancla`): en `MNV V₀`, `axiomsCodeT` vale `V₀`, que es por definición el valor del lado derecho de
`ax_axiomsCodeT_def`. Va por `rw` con lemas ∀ —⛔ ni `simp`, ni `decide`, ni un `rfl` que alcance el numeral
`nD`—, y el único `rfl` (`V₀_def`) compara dos expresiones idénticas tras desplegar `V₀` un nivel. No hace falta el
lema diagonal semántico.

`MN_axioms : ∀ v, contextSatisfies (MNV V₀) v axioms` — el modelo de los 142.

**§6 · El control negativo** (`control_tc_cons`, ADR‑124): el modelo NO valida cualquier cosa —refuta `ax_tc_cons`,
el axioma retirado que hizo INCONSISTENTE la teoría (ADR‑012)—. ⛔ Sus códigos cerrados (`strCodeM cons_sym`,
`numeralM 1`) no se evalúan: entran como TÉRMINOS variables de un lema `rfl`, y el argumento es la longitud de la
lista de argumentos (uno contra dos). La forma con `simp` sobre la hipótesis concreta no acababa (>3 GB a los 14 s; en
ADR‑119, >14 GB): según la bisección, el coste está en comprobar su prueba —el NÚCLEO, por inferencia, no medido—.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ROBINSON_PlusPlus.Meta.ModeloCodificacion

section Codificacion
open FOL
open FOL.Metamath.Semantics
open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.ModeloCodigo
open ROBINSON_PlusPlus.Meta.ModeloEstandar

variable {V : Nat}

/-! ## §3 · Los 107 de CODIFICACIÓN, validados

Todos con el mismo molde: `intro` de los binders, `abre`, y el lema de §1ter que dice lo que el axioma dice. -/

/-! ### Sustitución y lift sobre códigos de término (11) -/

theorem v_substtc_var_eq : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_substtc_var_eq := by
  intro v k s n; abre; intro h; rw [substtcN_var, if_pos h]
theorem v_substtc_var_gt : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_substtc_var_gt := by
  intro v k s n; abre; intro h; rw [substtcN_var, if_neg (Nat.ne_of_lt h), if_pos h]
theorem v_substtc_var_lt : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_substtc_var_lt := by
  intro v k s n; abre; intro h
  rw [substtcN_var, if_neg (by omega), if_neg (by omega)]
theorem v_substtc_func : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_substtc_func := by
  intro v k s a b; abre; exact substtcN_func k s a b
theorem v_substtsc_nil : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_substtsc_nil := by
  intro v k s; abre; exact substtscN_zero k s
theorem v_substtsc_cons : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_substtsc_cons := by
  intro v k s a b; abre; exact substtscN_consN k s a b
theorem v_liftc_var_lt : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_liftc_var_lt := by
  intro v c n; abre; intro h; rw [liftcN_var, if_pos h]
theorem v_liftc_var_ge : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_liftc_var_ge := by
  intro v c n; abre; intro h; rw [liftcN_var, if_neg (by omega)]
theorem v_liftc_func : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_liftc_func := by
  intro v c a b; abre; exact liftcN_func c a b
theorem v_liftsc_nil : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_liftsc_nil := by
  intro v c; abre; exact liftscN_zero c
theorem v_liftsc_cons : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_liftsc_cons := by
  intro v c a b; abre; exact liftscN_consN c a b

/-! ### Sustitución y lift sobre códigos de fórmula (16) -/

theorem v_substfc_bottom : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_substfc_bottom := by
  intro v x t; abre; exact substfcN_bot x t
theorem v_substfc_atom : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_substfc_atom := by
  intro v x t a b; abre; exact substfcN_atom x t a b
theorem v_substfc_eq : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_substfc_eq := by
  intro v x t a b; abre; exact substfcN_eq x t a b
theorem v_substfc_impl : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_substfc_impl := by
  intro v x t a b; abre; exact substfcN_impl x t a b
theorem v_substfc_forall : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_substfc_forall := by
  intro v x t a; abre; exact substfcN_forall x t a
theorem v_substfc_and : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_substfc_and := by
  intro v x t a b; abre; exact substfcN_and x t a b
theorem v_substfc_or : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_substfc_or := by
  intro v x t a b; abre; exact substfcN_or x t a b
theorem v_substfc_ex : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_substfc_ex := by
  intro v x t a; abre; exact substfcN_ex x t a
theorem v_liftfc_bottom : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_liftfc_bottom := by
  intro v c; abre; exact liftfcN_bot c
theorem v_liftfc_atom : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_liftfc_atom := by
  intro v c a b; abre; exact liftfcN_atom c a b
theorem v_liftfc_eq : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_liftfc_eq := by
  intro v c a b; abre; exact liftfcN_eq c a b
theorem v_liftfc_impl : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_liftfc_impl := by
  intro v c a b; abre; exact liftfcN_impl c a b
theorem v_liftfc_forall : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_liftfc_forall := by
  intro v c a; abre; exact liftfcN_forall c a
theorem v_liftfc_and : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_liftfc_and := by
  intro v c a b; abre; exact liftfcN_and c a b
theorem v_liftfc_or : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_liftfc_or := by
  intro v c a b; abre; exact liftfcN_or c a b
theorem v_liftfc_ex : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_liftfc_ex := by
  intro v c a; abre; exact liftfcN_ex c a

/-! ### Accesores (6) -/

theorem v_carc : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_carc := by
  intro v a b; abre; exact carN_consN a b
theorem v_cdrc : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_cdrc := by
  intro v a b; abre; exact cdrN_consN a b
theorem v_lenc_nil : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_lenc_nil := by
  intro v; unfold ax_lenc_nil; abre; exact lenN_zero
theorem v_lenc_cons : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_lenc_cons := by
  intro v a b; abre; exact lenN_consN a b
theorem v_nthc_zero : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_nthc_zero := by
  intro v a b; abre; exact nthN_cz a b
theorem v_nthc_succ : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_nthc_succ := by
  intro v a b i; abre; exact nthN_cs a b i

/-! ### `tcFn` y `runFn` (4) -/

theorem v_tc_zero : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_tc_zero := by
  intro v; unfold ax_tc_zero; abre; rfl
theorem v_tc_succ : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_tc_succ := by
  intro v n; abre; rfl
theorem v_runFn_nil : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_runFn_nil := by
  intro v c; abre; exact runFnN_zero c
theorem v_runFn_cons : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_runFn_cons := by
  intro v c l r; abre; exact runFnN_consN c l r

/-! ### `allIn` y `chainOk` (4) -/

theorem v_allIn_nil : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_allIn_nil := by
  intro v c; abre; exact allInN_zero c
theorem v_allIn_cons : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_allIn_cons := by
  intro v c a t; abre; exact ⟨(allInN_consN c a t).mp, (allInN_consN c a t).mpr⟩
theorem v_chainOk_nil : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_chainOk_nil := by
  intro v c; abre; exact chainOkN_zero _ c
theorem v_chainOk_cons : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_chainOk_cons := by
  intro v c l r; abre; exact ⟨(chainOkN_consN _ c l r).mp, (chainOkN_consN _ c l r).mpr⟩

/-! ### `validProofFn` (22): la conclusión la da `stepT`, sea cual sea la condición -/

/-- La línea `⟨K, …⟩` se consume por `vpfN_consN` y `stepT` la decide por su etiqueta. -/
local macro "vpf_paso" : tactic => `(tactic| (rw [vpfN_consN]; simp only [stepN, nthN_cz, nthN_cs, nthN_zero_l, stepT]))

theorem v_vpf_nil : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_vpf_nil := by
  intro v c; abre; exact vpfN_zero c
theorem v_vpf_p1 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_vpf_p1 := by
  intro v c a b r; abre; vpf_paso
theorem v_vpf_p2 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_vpf_p2 := by
  intro v c a b d r; abre; vpf_paso
theorem v_vpf_c1 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_vpf_c1 := by
  intro v c a b r; abre; vpf_paso
theorem v_vpf_c2 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_vpf_c2 := by
  intro v c a b r; abre; vpf_paso
theorem v_vpf_c3 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_vpf_c3 := by
  intro v c a b r; abre; vpf_paso
theorem v_vpf_j1 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_vpf_j1 := by
  intro v c a b r; abre; vpf_paso
theorem v_vpf_j2 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_vpf_j2 := by
  intro v c a b r; abre; vpf_paso
theorem v_vpf_j3 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_vpf_j3 := by
  intro v c a b d r; abre; vpf_paso
theorem v_vpf_efq : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_vpf_efq := by
  intro v c a r; abre; vpf_paso
theorem v_vpf_q1 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_vpf_q1 := by
  intro v c a b r; abre; vpf_paso
theorem v_vpf_q2 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_vpf_q2 := by
  intro v c a b r; abre; vpf_paso
theorem v_vpf_q3 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_vpf_q3 := by
  intro v c a b r; abre; vpf_paso
theorem v_vpf_eqrefl : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_vpf_eqrefl := by
  intro v c a r; abre; vpf_paso
theorem v_vpf_leibniz : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_vpf_leibniz := by
  intro v c a b d r; abre; vpf_paso
theorem v_vpf_p3 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_vpf_p3 := by
  intro v c a r; abre; vpf_paso
theorem v_vpf_mp : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_vpf_mp := by
  intro v c b a r; abre; intro _ _; vpf_paso
theorem v_vpf_gen : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_vpf_gen := by
  intro v c a r; abre; intro _; vpf_paso
theorem v_vpf_thy : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_vpf_thy := by
  intro v c a r; abre; intro _; vpf_paso
theorem v_vpf_ind : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_vpf_ind := by
  intro v c a r; abre; vpf_paso; rfl
theorem v_vpf_qconf : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_vpf_qconf := by
  intro v c a b r; abre; vpf_paso
theorem v_vpf_listInd : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_vpf_listInd := by
  intro v c a r; abre; vpf_paso; rfl

/-! ### `premsOf` (21) -/

local macro "prems" : tactic => `(tactic| ((simp only [premsOfN, nthN_cz, nthN_cs, nthN_zero_l]) <;> rfl))

theorem v_premsOf_mp : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_premsOf_mp := by
  intro v b a; abre; prems
theorem v_premsOf_gen : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_premsOf_gen := by
  intro v b a; abre; prems
theorem v_premsOf_thy : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_premsOf_thy := by
  intro v c; abre; prems
theorem v_premsOf_p1 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_premsOf_p1 := by
  intro v c a b; abre; prems
theorem v_premsOf_p2 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_premsOf_p2 := by
  intro v c a b d; abre; prems
theorem v_premsOf_c1 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_premsOf_c1 := by
  intro v c a b; abre; prems
theorem v_premsOf_c2 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_premsOf_c2 := by
  intro v c a b; abre; prems
theorem v_premsOf_c3 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_premsOf_c3 := by
  intro v c a b; abre; prems
theorem v_premsOf_j1 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_premsOf_j1 := by
  intro v c a b; abre; prems
theorem v_premsOf_j2 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_premsOf_j2 := by
  intro v c a b; abre; prems
theorem v_premsOf_j3 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_premsOf_j3 := by
  intro v c a b d; abre; prems
theorem v_premsOf_efq : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_premsOf_efq := by
  intro v c a; abre; prems
theorem v_premsOf_eqrefl : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_premsOf_eqrefl := by
  intro v c a; abre; prems
theorem v_premsOf_p3 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_premsOf_p3 := by
  intro v c a; abre; prems
theorem v_premsOf_q1 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_premsOf_q1 := by
  intro v c a b; abre; prems
theorem v_premsOf_q2 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_premsOf_q2 := by
  intro v c a b; abre; prems
theorem v_premsOf_q3 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_premsOf_q3 := by
  intro v c a b; abre; prems
theorem v_premsOf_leibniz : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_premsOf_leibniz := by
  intro v c a b d; abre; prems
theorem v_premsOf_ind : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_premsOf_ind := by
  intro v c a; abre; prems
theorem v_premsOf_qconf : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_premsOf_qconf := by
  intro v c a b; abre; prems
theorem v_premsOf_listInd : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_premsOf_listInd := by
  intro v c a; abre; prems

/-! ### `lineWF` (23): la RHS de cada etiqueta es, por construcción, la de `lineWFT` -/

local macro "lwf" : tactic => `(tactic| (intro h; exact ⟨(lineWFN_of_tag h (by decide)).mp, (lineWFN_of_tag h (by decide)).mpr⟩))

theorem v_lineWF_mp : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_lineWF_mp := by
  intro v x; abre; lwf
theorem v_lineWF_gen : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_lineWF_gen := by
  intro v x; abre; lwf
theorem v_lineWF_thy : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_lineWF_thy := by
  intro v x; abre; lwf
theorem v_lineWF_p1 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_lineWF_p1 := by
  intro v x; abre; lwf
theorem v_lineWF_p2 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_lineWF_p2 := by
  intro v x; abre; lwf
theorem v_lineWF_c1 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_lineWF_c1 := by
  intro v x; abre; lwf
theorem v_lineWF_c2 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_lineWF_c2 := by
  intro v x; abre; lwf
theorem v_lineWF_c3 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_lineWF_c3 := by
  intro v x; abre; lwf
theorem v_lineWF_j1 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_lineWF_j1 := by
  intro v x; abre; lwf
theorem v_lineWF_j2 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_lineWF_j2 := by
  intro v x; abre; lwf
theorem v_lineWF_j3 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_lineWF_j3 := by
  intro v x; abre; lwf
theorem v_lineWF_efq : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_lineWF_efq := by
  intro v x; abre; lwf
theorem v_lineWF_eqrefl : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_lineWF_eqrefl := by
  intro v x; abre; lwf
theorem v_lineWF_p3 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_lineWF_p3 := by
  intro v x; abre; lwf
theorem v_lineWF_q1 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_lineWF_q1 := by
  intro v x; abre; lwf
theorem v_lineWF_q2 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_lineWF_q2 := by
  intro v x; abre; lwf
theorem v_lineWF_q3 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_lineWF_q3 := by
  intro v x; abre; lwf
theorem v_lineWF_leibniz : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_lineWF_leibniz := by
  intro v x; abre; lwf
theorem v_lineWF_ind : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_lineWF_ind := by
  intro v x; abre; lwf
theorem v_lineWF_qconf : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_lineWF_qconf := by
  intro v x; abre; lwf
theorem v_lineWF_listInd : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_lineWF_listInd := by
  intro v x; abre; lwf

theorem v_lineWF_inv : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_lineWF_inv := by
  intro v x; abre; intro h
  have h1 : nthN x 1 < 21 := h.1
  rw [show (0 : Nat) + 1 = 1 from rfl]
  omega

theorem v_lineWF_cons : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_lineWF_cons := by
  intro v x; abre; intro h
  by_cases hx : x = 0
  · exfalso
    subst hx
    have h2 := h.2
    rw [nthN_zero_l] at h2
    have h3 : lenN 0 = 4 := h2.1
    rw [lenN_zero] at h3
    exact absurd h3 (by decide)
  · exact (consN_car_cdr hx).symm

/-! ## §4 · EL ANCLA, por `rw` con lemas ∀ (⛔ nada de `simp`, `decide` ni `rfl` que alcance `nD`)

Su lado derecho no nombra `axiomsCodeT`, y `(MNV V)` interpreta `axiomsCodeT` por `V₀`, que es por definición el valor
de ese lado derecho. Cada paso instancia un lema universal; el único `rfl` (`V₀_def`) compara dos expresiones
IDÉNTICAS tras desplegar `V₀` un nivel. -/

theorem ev_concat (v : Nat → Nat) (a b : Term) :
    evalTerm (MNV V) v (concat a b) = concatN (evalTerm (MNV V) v a) (evalTerm (MNV V) v b) := rfl
theorem ev_cons (v : Nat → Nat) (a b : Term) :
    evalTerm (MNV V) v (cons a b) = consN (evalTerm (MNV V) v a) (evalTerm (MNV V) v b) := rfl
theorem ev_nil (v : Nat → Nat) : evalTerm (MNV V) v nil = 0 := rfl
theorem ev_zero (v : Nat → Nat) : evalTerm (MNV V) v zero = 0 := rfl
theorem ev_substfc (v : Nat → Nat) (a b c : Term) :
    evalTerm (MNV V) v (substfc a b c) = substfcN (evalTerm (MNV V) v a) (evalTerm (MNV V) v b) (evalTerm (MNV V) v c) := rfl
theorem ev_tcFn (v : Nat → Nat) (a : Term) : evalTerm (MNV V) v (tcFn a) = tcFnN (evalTerm (MNV V) v a) := rfl
theorem ev_axiomsCodeT (v : Nat → Nat) : evalTerm (MNV V) v axiomsCodeT = V := rfl

theorem V₀_def : V₀ = concatN (codeNatList axiomsBase)
    (consN (substfcN 0 (tcFnN (codeNat (psiD axiomsBase))) (codeNat (psiD axiomsBase))) 0) := rfl

theorem v_ancla : ∀ v : Nat → Nat, evalFormula (MNV V₀) v ax_axiomsCodeT_def := by
  intro v
  rw [ax_axiomsCodeT_def, axD]
  show evalTerm (MNV V₀) v axiomsCodeT =
    evalTerm (MNV V₀) v (concat (listFormCodeM axiomsBase) (cons (deltaD axiomsBase) nil))
  rw [ev_axiomsCodeT, ev_concat, ev_cons, ev_nil, ev_listFormCodeM, deltaD, ev_substfc, ev_zero, ev_tcFn, nD,
    ev_numeralM]
  exact V₀_def

/-! ## §5 · LOS 142 -/

theorem MN_codingAxioms (v : Nat → Nat) : ∀ φ, List.Mem φ codingAxioms → evalFormula (MNV V) v φ := by
  unfold codingAxioms
  exact mem_cons_elim (v_substtc_var_eq v) (mem_cons_elim (v_substtc_var_gt v) (mem_cons_elim (v_substtc_var_lt v) (mem_cons_elim (v_substtc_func v) (mem_cons_elim (v_substtsc_nil v) (mem_cons_elim (v_substtsc_cons v) (mem_cons_elim (v_liftc_var_lt v) (mem_cons_elim (v_liftc_var_ge v) (mem_cons_elim (v_liftc_func v) (mem_cons_elim (v_liftsc_nil v) (mem_cons_elim (v_liftsc_cons v) (mem_cons_elim (v_substfc_bottom v) (mem_cons_elim (v_substfc_atom v) (mem_cons_elim (v_substfc_eq v) (mem_cons_elim (v_substfc_impl v) (mem_cons_elim (v_substfc_forall v) (mem_cons_elim (v_substfc_and v) (mem_cons_elim (v_substfc_or v) (mem_cons_elim (v_substfc_ex v) (mem_cons_elim (v_liftfc_bottom v) (mem_cons_elim (v_liftfc_atom v) (mem_cons_elim (v_liftfc_eq v) (mem_cons_elim (v_liftfc_impl v) (mem_cons_elim (v_liftfc_forall v) (mem_cons_elim (v_liftfc_and v) (mem_cons_elim (v_liftfc_or v) (mem_cons_elim (v_liftfc_ex v) (mem_cons_elim (v_carc v) (mem_cons_elim (v_cdrc v) (mem_cons_elim (v_vpf_nil v) (mem_cons_elim (v_vpf_p1 v) (mem_cons_elim (v_vpf_p2 v) (mem_cons_elim (v_vpf_c1 v) (mem_cons_elim (v_vpf_c2 v) (mem_cons_elim (v_vpf_c3 v) (mem_cons_elim (v_vpf_j1 v) (mem_cons_elim (v_vpf_j2 v) (mem_cons_elim (v_vpf_j3 v) (mem_cons_elim (v_vpf_efq v) (mem_cons_elim (v_vpf_q1 v) (mem_cons_elim (v_vpf_q2 v) (mem_cons_elim (v_vpf_q3 v) (mem_cons_elim (v_vpf_eqrefl v) (mem_cons_elim (v_vpf_leibniz v) (mem_cons_elim (v_vpf_p3 v) (mem_cons_elim (v_vpf_mp v) (mem_cons_elim (v_vpf_gen v) (mem_cons_elim (v_vpf_thy v) (mem_cons_elim (v_vpf_ind v) (mem_cons_elim (v_vpf_qconf v) (mem_cons_elim (v_vpf_listInd v) (mem_cons_elim (v_tc_zero v) (mem_cons_elim (v_tc_succ v) (mem_cons_elim (v_runFn_nil v) (mem_cons_elim (v_runFn_cons v) (mem_cons_elim (v_allIn_nil v) (mem_cons_elim (v_allIn_cons v) (mem_cons_elim (v_chainOk_nil v) (mem_cons_elim (v_chainOk_cons v) (mem_cons_elim (v_lineWF_mp v) (mem_cons_elim (v_premsOf_mp v) (mem_cons_elim (v_lineWF_gen v) (mem_cons_elim (v_premsOf_gen v) (mem_cons_elim (v_lineWF_thy v) (mem_cons_elim (v_premsOf_thy v) (mem_cons_elim (v_lineWF_p1 v) (mem_cons_elim (v_premsOf_p1 v) (mem_cons_elim (v_lineWF_p2 v) (mem_cons_elim (v_premsOf_p2 v) (mem_cons_elim (v_lineWF_c1 v) (mem_cons_elim (v_premsOf_c1 v) (mem_cons_elim (v_lineWF_c2 v) (mem_cons_elim (v_premsOf_c2 v) (mem_cons_elim (v_lineWF_c3 v) (mem_cons_elim (v_premsOf_c3 v) (mem_cons_elim (v_lineWF_j1 v) (mem_cons_elim (v_premsOf_j1 v) (mem_cons_elim (v_lineWF_j2 v) (mem_cons_elim (v_premsOf_j2 v) (mem_cons_elim (v_lineWF_j3 v) (mem_cons_elim (v_premsOf_j3 v) (mem_cons_elim (v_lineWF_efq v) (mem_cons_elim (v_premsOf_efq v) (mem_cons_elim (v_lineWF_eqrefl v) (mem_cons_elim (v_premsOf_eqrefl v) (mem_cons_elim (v_lineWF_p3 v) (mem_cons_elim (v_premsOf_p3 v) (mem_cons_elim (v_lineWF_q1 v) (mem_cons_elim (v_premsOf_q1 v) (mem_cons_elim (v_lineWF_q2 v) (mem_cons_elim (v_premsOf_q2 v) (mem_cons_elim (v_lineWF_q3 v) (mem_cons_elim (v_premsOf_q3 v) (mem_cons_elim (v_lineWF_leibniz v) (mem_cons_elim (v_premsOf_leibniz v) (mem_cons_elim (v_lineWF_ind v) (mem_cons_elim (v_premsOf_ind v) (mem_cons_elim (v_lineWF_qconf v) (mem_cons_elim (v_premsOf_qconf v) (mem_cons_elim (v_lineWF_listInd v) (mem_cons_elim (v_premsOf_listInd v) (mem_cons_elim (v_lenc_nil v) (mem_cons_elim (v_lenc_cons v) (mem_cons_elim (v_nthc_zero v) (mem_cons_elim (v_nthc_succ v) (mem_cons_elim (v_lineWF_inv v) (mem_cons_elim (v_lineWF_cons v) (mem_nil_elim)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem MN_axioms (v : Nat → Nat) : contextSatisfies (MNV V₀) v axioms := by
  intro φ hφ
  rw [axioms_split] at hφ
  cases List.mem_append.mp hφ with
  | inl h =>
    cases List.mem_append.mp h with
    | inl h1 => exact MN_coreAxioms v φ h1
    | inr h2 => exact MN_codingAxioms v φ h2
  | inr h =>
    have e : φ = ax_axiomsCodeT_def := List.mem_singleton.mp h
    rw [e]; exact v_ancla v

/-! ## §6 · CONTROL NEGATIVO: el modelo no valida cualquier cosa

`ax_tc_cons` (`tcFn (cons a b) = ⟨1, ⌜::⌝, [tcFn a, tcFn b]⟩`) es el axioma que hizo INCONSISTENTE la teoría y se
retiró de la lista (ADR‑012). `MNV V` lo REFUTA: `cons a b` vale un sucesor, y `tcFnN` de un sucesor es el código de
`σ(·)`, cuya lista de argumentos tiene UNO; el axioma le pide DOS.

⛔ Sin evaluar un solo código: `strCodeM cons_sym` y `numeralM 1` entran como términos VARIABLES (`N`, `S`) de un lema
`rfl`, y `tcFnN_consN_ne` vale para todo `a`, `b`, `N`, `X`. La forma con `simp only` sobre la hipótesis concreta
elabora (con un `sorry` que no usa la hipótesis, 4 s), pero en cuanto su prueba entra en el término pasa de 3 GB a
los 14 s sin acabar (medido, ADR‑124); que el coste sea el NÚCLEO comprobándola es una inferencia de esa bisección
(ADR‑127). -/

theorem tcFnN_succ (n : Nat) :
    tcFnN (n + 1) = consN 1 (consN (codeNatStr succ_sym) (consN (consN (tcFnN n) 0) 0)) := rfl

/-- `tcFnN` de un sucesor tiene UN argumento; `ax_tc_cons` le pide DOS —para todo `a`, `b`, etiqueta `N` y símbolo
    `X`—. -/
theorem tcFnN_consN_ne (a b N X : Nat) :
    tcFnN (consN a b) ≠ consN N (consN X (consN (consN (tcFnN a) (consN (tcFnN b) 0)) 0)) := by
  intro h
  rw [show consN a b = triN (a + b) + b + 1 from rfl, tcFnN_succ] at h
  have h2 := (ROBINSON_PlusPlus.Meta.CodeNatInjPrf.consN_inj h).2
  have h3 := (ROBINSON_PlusPlus.Meta.CodeNatInjPrf.consN_inj h2).2
  have h4 := (ROBINSON_PlusPlus.Meta.CodeNatInjPrf.consN_inj h3).1
  have h5 := (ROBINSON_PlusPlus.Meta.CodeNatInjPrf.consN_inj h4).2
  exact ROBINSON_PlusPlus.Meta.CodeNatInjPrf.consN_ne_zero _ _ h5.symm

theorem ev_tc_cons_izq (v : Nat → Nat) :
    evalTerm (MNV V) v (tcFn (cons (.var 1) (.var 0))) = tcFnN (consN (v 1) (v 0)) := rfl

theorem ev_tc_cons_der (v : Nat → Nat) (N S : Term) :
    evalTerm (MNV V) v (cons N (cons S (cons (cons (tcFn (.var 1)) (cons (tcFn (.var 0)) nil)) nil)))
      = consN (evalTerm (MNV V) v N) (consN (evalTerm (MNV V) v S)
          (consN (consN (tcFnN (v 1)) (consN (tcFnN (v 0)) 0)) 0)) := rfl

/-- ⛔ **Control negativo**: `MNV V` REFUTA `ax_tc_cons`, el axioma que hizo inconsistente la teoría (ADR‑012). -/
theorem control_tc_cons : ¬ ∀ v : Nat → Nat, evalFormula (MNV V) v ax_tc_cons := by
  intro h
  have h1 : evalTerm (MNV V) (shiftEnv (shiftEnv (fun _ => 0) 0) 0) (tcFn (cons (.var 1) (.var 0)))
      = evalTerm (MNV V) (shiftEnv (shiftEnv (fun _ => 0) 0) 0) (cons (numeralM 1) (cons (strCodeM cons_sym)
          (cons (cons (tcFn (.var 1)) (cons (tcFn (.var 0)) nil)) nil))) := h (fun _ => 0) 0 0
  rw [ev_tc_cons_izq, ev_tc_cons_der] at h1
  exact tcFnN_consN_ne _ _ _ _ h1

end Codificacion

end ROBINSON_PlusPlus.Meta.ModeloCodificacion

#print axioms ROBINSON_PlusPlus.Meta.ModeloCodificacion.MN_codingAxioms
#print axioms ROBINSON_PlusPlus.Meta.ModeloCodificacion.v_ancla
#print axioms ROBINSON_PlusPlus.Meta.ModeloCodificacion.MN_axioms

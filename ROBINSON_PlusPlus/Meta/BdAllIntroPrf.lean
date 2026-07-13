/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.D3InDotPrf
import ROBINSON_PlusPlus.Meta.PropCodePrf

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.Sigma1Prf
open ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
open ROBINSON_PlusPlus.Meta.MpCodePrf
open ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf
open ROBINSON_PlusPlus.Meta.NumCodeClosedPrf
open ROBINSON_PlusPlus.Meta.TrackedCorePrf
open ROBINSON_PlusPlus.Meta.TcArithPrf
open ROBINSON_PlusPlus.Meta.NatArithPrf
open ROBINSON_PlusPlus.Meta.BoundedInPrf
open ROBINSON_PlusPlus.Meta.EvalArithPrf
open ROBINSON_PlusPlus.Meta.EvalLtPrf
open ROBINSON_PlusPlus.Meta.EvalBoundedPrf
open ROBINSON_PlusPlus.Meta.PropCodePrf
open ROBINSON_PlusPlus.Meta.D3InDotPrf

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace ROBINSON_PlusPlus.Meta.BdAllIntroPrf

/-!
## META — NIVEL D real (§40): INTRODUCCIÓN del `∀` acotado a nivel de código

La pieza que §30 dejó pendiente (`pcc_bdAll_elim` existía; la **intro** no) y que `hC_dot` necesita:
`chainOkB nil p = ∀i<lenc p. lineOkB nil p i`, así que reflejarlo pide construir `Prov(⌜∀i<Ḃ. φ(i)⌝)`.

**Por qué hace falta inducción.** El truco estándar (Hájek‑Pudlák) reduce `∀i<n̄. φ(i)` a la
**disyunción finita** `i=0̄ ∨ … ∨ i=(n−1)̄`, válida en Q para un numeral **concreto** `n̄`. Aquí la cota
es `lenc p` con `p` **abstracto** — su dotado `tcFn (lenc p)` **no es un numeral concreto** ⇒ el truco
no aplica y hay que inducir de verdad.

**Sobre qué se induce.** *No* sobre el testigo (`Ac[x] ⇒ Ac[σx]` es falso: `φ(σx)` no se sigue de
`φ(x)`), sino **sobre la COTA**, a nivel **objeto** (`prf_nat_induction`), con guarda `b < σ bnd`: en el
paso, la guarda da `b < bnd`, y de ahí `hbody b` entrega justamente el `Prov(⌜φ(ḃ)⌝)` que falta.

**Truco estructural clave.** `pcc_gen_code (body) : Prov(⌜body⌝) ⇒ Prov(⌜∀body⌝)` toma el body
**abierto**, así que se induce sobre el **CUERPO ABIERTO** (hueco fijado a `⌜v₀⌝`) y se aplica `gen`
**una sola vez al final**. Esto evita el *round‑trip* `∀`‑elim, que reintroduciría el problema de la
sustitución identidad (`substfc` **decrementa** las variables superiores, `prf_substtc_var_gt`).
-/

/-! ### Congruencias que faltaban -/

/-- Congruencia de `orc` (espejo de `prf_congr_andc`). -/
theorem prf_congr_orc {a a' b b' : Term} (ha : Prf (a =eq a')) (hb : Prf (b =eq b')) :
    Prf (orc a b =eq orc a' b') := by
  unfold orc
  exact prf_congr_cons_tail
    (prf_eq_trans (prf_congr_cons_head ha) (prf_congr_cons_tail (prf_congr_cons_head hb)))

/-- Congruencia de `substfc` en el código (3er arg), en `PrfH` (espejo de `PrfH_congr_substtc3`). -/
theorem PrfH_congr_substfc3 {Γ : List Formula} {v s a b : Term} (h : PrfH Γ (a =eq b)) :
    PrfH Γ (substfc v s a =eq substfc v s b) := by
  let f : Formula := Formula.eq (substfc (liftTerm 0 v) (liftTerm 0 s) (liftTerm 0 a))
                                (substfc (liftTerm 0 v) (liftTerm 0 s) (.var 0))
  have hS : ∀ u : Term, substFormula 0 u f = Formula.eq (substfc v s a) (substfc v s u) := by
    intro u
    simp only [f, substfc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS b) ▸ PrfH_leibniz_subst (A := f) h ((hS a) ▸ prf_to_prfH (prf_refl (substfc v s a)) Γ)

/-- Congruencia de `substfc` en el código (3er arg). -/
theorem prf_congr_substfc3 {v s a b : Term} (h : Prf (a =eq b)) :
    Prf (substfc v s a =eq substfc v s b) :=
  prfH_nil_to_prf (PrfH_congr_substfc3 (Γ := []) (prf_to_prfH h [])) rfl

/-! ### Piezas objeto de `<` que faltaban -/

/-- **`m < n ⇒ m < σn`**: mismo testigo desplazado (`k ↦ σk`); `m + σ(σk) =eq σ(m + σk) =eq σn`. -/
theorem prf_lt_succ_of_lt (m n : Term) : Prf (lt m n ⇒ lt m (succ n)) := by
  have himp : Prf (Formula.ex (Formula.eq (add (liftTerm 0 m) (succ (.var 0))) (liftTerm 0 n))
      ⇒ lt m (succ n)) := by
    refine prf_ex_elim_imp ?_
    show PrfH [Formula.eq (add (liftTerm 0 m) (succ (.var 0))) (liftTerm 0 n)]
      (lt (liftTerm 0 m) (succ (liftTerm 0 n)))
    refine PrfH_lt_intro (liftTerm 0 m) (succ (liftTerm 0 n)) (succ (.var 0)) ?_
    exact PrfH_eq_trans
      (prf_to_prfH (prf_add_succ_t (liftTerm 0 m) (succ (.var 0))) _)
      (PrfH_eq_congr_succ (prfH_hyp_self _))
  exact prf_deduction
    (PrfH.mp _ _ _ (prf_to_prfH himp _) (PrfH_iff_mp (prf_lt_iff m n) (prfH_hyp_self _)))

/-- **Split VOLTEADO**: `i < σb ⇒ (i < b) ∨ (b = i)`. La igualdad va **`b = i`** (no `i = b`): el
    Leibniz interno del paso necesita ese antecedente, y la simetría interna NO es aplicable aquí
    (exige el 1er argumento `substtc`‑invariante, cosa que `⌜v₀⌝` **no** es). Se voltea en el OBJETO. -/
theorem prf_lt_succ_split' (i b : Term) :
    Prf (lt i (succ b) ⇒ lor (lt i b) (Formula.eq b i)) := by
  refine prf_deduction ?_
  have hsplit : PrfH [lt i (succ b)] (lor (lt i b) (Formula.eq i b)) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_lt_succ_split i b) _) (prfH_hyp_self _)
  refine PrfH_or_elim hsplit ?_ ?_
  · exact PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.j1 (lt i b) (Formula.eq b i)))
      (PrfH.hyp _ _ (List.Mem.head _))
  · exact PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.j2 (lt i b) (Formula.eq b i)))
      (PrfH_eq_symm (PrfH.hyp _ _ (List.Mem.head _)))

/-! ### Simetría interna de `=` (forma INTERNA, no externa) -/

/-- **Simetría interna de `=` a nivel de código, forma INTERNA**: `⊢ Prov(⌜(X=Y) ⇒ (Y=X)⌝)`.
    Leibniz con `Ac := (v₀ = X)` da `Prov(⌜(X=Y) ⇒ ((X=X) ⇒ (Y=X))⌝)`; la reflexividad codificada y
    P2 descargan el `(X=X)`. **Exige `X` `substtc`‑invariante** (por eso NO sirve con `X = ⌜v₀⌝`). -/
theorem pcc_eq_symm_code_internal (X Y : Term) (hX : ∀ W, Prf (substtc zero W X =eq X)) :
    Prf (provFromCode (implc (eqc X Y) (eqc Y X))) := by
  have hcomp : ∀ t : Term,
      Prf (substfc zero t (eqc (varc (numeral 0)) X) =eq eqc t X) := fun t =>
    prf_eq_trans (prf_substfc_eq zero t (varc (numeral 0)) X)
      (prf_congr_eqCodeFn (prf_substtc_varc0 t) (hX t))
  have hleib : Prf (provFromCode (implc (eqc X Y)
      (implc (substfc zero X (eqc (varc (numeral 0)) X))
             (substfc zero Y (eqc (varc (numeral 0)) X))))) :=
    pcc_leibniz_code (eqc (varc (numeral 0)) X) X Y
  have hleib2 : Prf (provFromCode (implc (eqc X Y) (implc (eqc X X) (eqc Y X)))) :=
    prf_mp (prf_provCode_congr
      (prf_congr_implc (prf_refl _) (prf_congr_implc (hcomp X) (hcomp Y)))) hleib
  exact pcc_mp_code_apply
    (pcc_mp_code_apply (pcc_p2_code (eqc X Y) (eqc X X) (eqc Y X)) hleib2)
    (pcc_weaken_code (eqc X Y) (eqc X X) (prf_provFromCode_eqCodeFn_refl X))

/-! ### El `∀` acotado: BASE y PASO -/

/-- **BASE**: `⊢ Prov(⌜(v₀ < 0̇) ⇒ Psi⌝)` — **vacuo**, como debe ser. Codifica `∀x. ¬(x<0)`
    (instanciado en el propio `⌜v₀⌝`), puentea `termCode 0 → tcFn 0` (`prf_tc_zero`) y compone con
    **EFQ** por silogismo hipotético. -/
theorem pcc_bdAll_base (Psi : Term) :
    Prf (provFromCode (implc (ltCodeFn (varc (numeral 0)) (tcFn zero)) Psi)) := by
  have hthm : Prf (Formula.forall (Formula.impl (lt (.var 0) zero) Formula.bottom)) :=
    Prf.gen _ (prf_not_lt_zero (.var 0))
  have hinst : Prf (provFromCode (substfc zero (varc (numeral 0))
      (formCode (Formula.impl (lt (.var 0) zero) Formula.bottom)))) :=
    pcc_thm_inst _ hthm (varc (numeral 0))
  have hbridge : Prf (substfc zero (varc (numeral 0))
      (formCode (Formula.impl (lt (.var 0) zero) Formula.bottom))
      =eq implc (ltCodeFn (varc (numeral 0)) (termCode zero)) botc) :=
    prf_substfc_arith_open 0 (varc (numeral 0)) (Formula.impl (lt (.var 0) zero) Formula.bottom)
  have hnlt : Prf (provFromCode (implc (ltCodeFn (varc (numeral 0)) (termCode zero)) botc)) :=
    prf_mp (prf_provCode_congr hbridge) hinst
  have hnlt2 : Prf (provFromCode (implc (ltCodeFn (varc (numeral 0)) (tcFn zero)) botc)) :=
    prf_mp (prf_provCode_congr
      (prf_congr_implc (prf_congr_atom2CodeFn (prf_refl _) (prf_eq_symm prf_tc_zero))
        (prf_refl _)))
      hnlt
  exact pcc_imp_trans_code _ botc Psi hnlt2 (pcc_efq_code Psi)

/-- Esquema objeto del split volteado: `#0 = i` (índice), `#1 = b` (cota). -/
def splitSchema : Formula :=
  Formula.impl (lt (.var 0) (succ (.var 1)))
    (lor (lt (.var 0) (.var 1)) (Formula.eq (.var 1) (.var 0)))

/-- **SPLIT codificado**: `⊢ Prov(⌜ (v₀ < (σb)˙) ⇒ ((v₀ < ḃ) ∨ (ḃ = v₀)) ⌝)`.
    `pcc_thm_inst2` con DOS testigos (`tcFn b` para la cota, `⌜v₀⌝` para el índice); el `substfc`
    interno computa por `rfl` (arith_open a nivel 1) y el **externo es la IDENTIDAD** sobre ese código
    concreto (su única code‑var es `⌜v₀⌝`, y el resto es `substtc`‑invariante). Puentes finales:
    `prf_liftc_tcFn` y `prf_tc_succ'`. -/
theorem pcc_lt_succ_split_code (b : Term) :
    Prf (provFromCode (implc (ltCodeFn (varc (numeral 0)) (tcFn (succ b)))
      (orc (ltCodeFn (varc (numeral 0)) (tcFn b))
           (eqCodeFn (tcFn b) (varc (numeral 0)))))) := by
  have hWinv : ∀ W, Prf (substtc zero W (liftc zero (tcFn b)) =eq liftc zero (tcFn b)) :=
    substtc_inv_liftc_tcFn b
  have hSWinv : ∀ W, Prf (substtc zero W (succcT (liftc zero (tcFn b)))
      =eq succcT (liftc zero (tcFn b))) := substtc_inv_succcT hWinv
  have hthm : Prf (forall_2 splitSchema) :=
    Prf.gen _ (Prf.gen _ (prf_lt_succ_split' (.var 0) (.var 1)))
  have hinst : Prf (provFromCode (substfc zero (varc (numeral 0))
      (substfc (succ zero) (liftc zero (tcFn b)) (formCode splitSchema)))) :=
    pcc_thm_inst2 splitSchema hthm (tcFn b) (varc (numeral 0))
  have hin : Prf (substfc (succ zero) (liftc zero (tcFn b)) (formCode splitSchema)
      =eq implc (ltCodeFn (varc (numeral 0)) (succcT (liftc zero (tcFn b))))
        (orc (ltCodeFn (varc (numeral 0)) (liftc zero (tcFn b)))
             (eqCodeFn (liftc zero (tcFn b)) (varc (numeral 0))))) :=
    prf_substfc_arith_open 1 (liftc zero (tcFn b)) splitSchema
  have hinst2 := prf_mp (prf_provCode_congr (prf_congr_substfc3 hin)) hinst
  have hid : Prf (substfc zero (varc (numeral 0))
      (implc (ltCodeFn (varc (numeral 0)) (succcT (liftc zero (tcFn b))))
        (orc (ltCodeFn (varc (numeral 0)) (liftc zero (tcFn b)))
             (eqCodeFn (liftc zero (tcFn b)) (varc (numeral 0)))))
      =eq implc (ltCodeFn (varc (numeral 0)) (succcT (liftc zero (tcFn b))))
        (orc (ltCodeFn (varc (numeral 0)) (liftc zero (tcFn b)))
             (eqCodeFn (liftc zero (tcFn b)) (varc (numeral 0))))) := by
    refine prf_eq_trans (prf_substfc_impl zero (varc (numeral 0)) _ _) ?_
    refine prf_congr_implc (prf_substfc_ltCodeFn_varc0 _ (varc (numeral 0)) hSWinv) ?_
    refine prf_eq_trans (prf_substfc_or zero (varc (numeral 0)) _ _) ?_
    refine prf_congr_orc (prf_substfc_ltCodeFn_varc0 _ (varc (numeral 0)) hWinv) ?_
    refine prf_eq_trans (prf_substfc_eq zero (varc (numeral 0)) _ _) ?_
    exact prf_congr_eqCodeFn (hWinv (varc (numeral 0))) (prf_substtc_varc0 _)
  have hinst3 := prf_mp (prf_provCode_congr hid) hinst2
  exact prf_mp (prf_provCode_congr
    (prf_congr_implc
      (prf_congr_atom2CodeFn (prf_refl _)
        (prf_eq_trans (prf_congr_succcT (prf_liftc_tcFn b)) (prf_eq_symm (prf_tc_succ' b))))
      (prf_congr_orc
        (prf_congr_atom2CodeFn (prf_refl _) (prf_liftc_tcFn b))
        (prf_congr_eqCodeFn (prf_liftc_tcFn b) (prf_refl _)))))
    hinst3

/-- **PASO**: de la HI `Prov(⌜(v₀ < ḃ) ⇒ Psi⌝)` y `Prov(⌜Psi[ḃ]⌝)` sale `Prov(⌜(v₀ < (σb)˙) ⇒ Psi⌝)`.

    `hPsiId` («sustituir `⌜v₀⌝` por sí mismo en `Psi` es la identidad») es **necesaria**: `substfc`
    DECREMENTA las variables superiores (`prf_substtc_var_gt`), luego `substfc 0 ⌜v₀⌝ Psi` sólo es la
    identidad cuando la única code‑var de `Psi` es `⌜v₀⌝` — que es el caso de uso. Se descarga
    estructuralmente en la aplicación (patrón `prf_substfc_ltCodeFn_varc0`). -/
theorem pcc_bdAll_step (Psi b : Term)
    (hPsiId : Prf (substfc zero (varc (numeral 0)) Psi =eq Psi))
    (hIH : Prf (provFromCode (implc (ltCodeFn (varc (numeral 0)) (tcFn b)) Psi)))
    (hb : Prf (provFromCode (substfc zero (tcFn b) Psi))) :
    Prf (provFromCode (implc (ltCodeFn (varc (numeral 0)) (tcFn (succ b))) Psi)) := by
  have hleib : Prf (provFromCode (implc (eqc (tcFn b) (varc (numeral 0)))
      (implc (substfc zero (tcFn b) Psi) (substfc zero (varc (numeral 0)) Psi)))) :=
    pcc_leibniz_code Psi (tcFn b) (varc (numeral 0))
  have hleib2 : Prf (provFromCode (implc (eqc (tcFn b) (varc (numeral 0)))
      (implc (substfc zero (tcFn b) Psi) Psi))) :=
    prf_mp (prf_provCode_congr
      (prf_congr_implc (prf_refl _) (prf_congr_implc (prf_refl _) hPsiId))) hleib
  have hcaseB : Prf (provFromCode (implc (eqc (tcFn b) (varc (numeral 0))) Psi)) :=
    pcc_mp_code_apply
      (pcc_mp_code_apply (pcc_p2_code (eqc (tcFn b) (varc (numeral 0)))
        (substfc zero (tcFn b) Psi) Psi) hleib2)
      (pcc_weaken_code (eqc (tcFn b) (varc (numeral 0))) (substfc zero (tcFn b) Psi) hb)
  have hor : Prf (provFromCode (implc
      (orc (ltCodeFn (varc (numeral 0)) (tcFn b)) (eqCodeFn (tcFn b) (varc (numeral 0)))) Psi)) :=
    pcc_or_elim_imp_code _ _ Psi hIH hcaseB
  exact pcc_imp_trans_code _ _ Psi (pcc_lt_succ_split_code b) hor

end ROBINSON_PlusPlus.Meta.BdAllIntroPrf

export ROBINSON_PlusPlus.Meta.BdAllIntroPrf (
  prf_congr_orc PrfH_congr_substfc3 prf_congr_substfc3
  prf_lt_succ_of_lt prf_lt_succ_split' pcc_eq_symm_code_internal
  pcc_bdAll_base splitSchema pcc_lt_succ_split_code pcc_bdAll_step
)
